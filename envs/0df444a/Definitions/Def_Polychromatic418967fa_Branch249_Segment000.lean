-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch249_Segment000
-- name    : Polychromatic418967fa_Branch249_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:39:21.491165+00:00
-- url     : https://prove2.me/theorems/6d78772b-817e-4238-ad44-39c0680116aa
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

def Polychromatic418967fa.branch_249_segment_000 : allB 100 249 :=
  allB_succ 99 249 (allA_succ_of_accept 98 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 97 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 249 3 32 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630 95 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 249 3 31 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 249
  (Polychromatic418967fa.accept_16_12_3_9_1_5886 92 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 91 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 249 3 30 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 89
  99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 249
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 88 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 249 3 29 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 85 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 249 3 28 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 249
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 83 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 249 3 27 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 80
  99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 79 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 249 3 26 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 249 (Polychromatic418967fa.accept_16_12_3_9_1_5886 76 99
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 249 3 25 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 249 3 24 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  71 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 249 3 23 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 67 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 249 3 22 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 249
  (Polychromatic418967fa.accept_12_5_3_9_1_541 65 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 249 (Polychromatic418967fa.accept_18_10_9_15_1_7267 64 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 249 3 21 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 249 3 20 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 249 3 19 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 249
  (Polychromatic418967fa.accept_19_18_4_2_1_2841 56 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 249 3 18 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 53
  99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 52 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 249 3 17 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 249 3 16 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 249 3 15 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 249 (Polychromatic418967fa.accept_16_12_3_9_1_5886
  44 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 249 3 14 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 249 3 13 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 249 3 12 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 249 3 11 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 249 (Polychromatic418967fa.accept_13_6_8_2_1_1484 32 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 249 3 10 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 249
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 249 (Polychromatic418967fa.accept_16_12_3_9_1_5886 28 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 249 3 9 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 249 3 8 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 249 3 7 33 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 249
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 249 3 6 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 249
  (Polychromatic418967fa.accept_17_16_14_11_1_7836 16 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 99 249 3 5 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 249 (Polychromatic418967fa.accept_12_1_3_9_1_174
  13 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 249 3 4 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 249
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 249 3 3 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 249 (Polychromatic418967fa.accept_17_8_14_11_1_9101 8 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 249 3 2 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 249 (Polychromatic418967fa.accept_14_4_1_11_1_5026 4 99 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 249 3 1 33 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 99 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  249 (allA_succ_of_accept 97 98 249 (accept_3_4 97 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 249 (Polychromatic418967fa.accept_13_5_7_2_1_852 96 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 249 (accept_3_4 94 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 93 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 92 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 249 (accept_3_4 91 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 90 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 249 (accept_3_4 88 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 86 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 249 (accept_3_4 85 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 84 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 249 (accept_3_4 82 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 249 (Polychromatic418967fa.accept_10_1_8_9_1_787 81 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 249
  (Polychromatic418967fa.accept_11_3_10_7_1_129 80 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 249 (accept_3_4 79 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 249 (accept_3_4 76 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 249 (accept_3_4 73 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 249 (Polychromatic418967fa.accept_21_9_14_18_1_7576 72 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 249 (accept_3_4 70 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 249 (Polychromatic418967fa.accept_11_3_10_7_1_129 69 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 249 (accept_3_4 67 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 249 (accept_3_4 64 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 249
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 62 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 249 (accept_3_4 61 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 249 (Polychromatic418967fa.accept_13_8_7_2_1_2988 60 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 249 (accept_3_4 58 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 249 (accept_3_4 55 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 249 (accept_3_4 52 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 249 (accept_3_4 49 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 249 (accept_3_4 46 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 249 (Polychromatic418967fa.accept_24_21_2_9_1_9974 45 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 249
  (Polychromatic418967fa.accept_10_4_8_9_1_784 44 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 249 (accept_3_4 43 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 249 (accept_3_4 40 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 249 (accept_3_4 37 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 249 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 249 (accept_3_4 34 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 249 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 249 (accept_3_4 31 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 249 (accept_3_4 28 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 249
  (Polychromatic418967fa.accept_21_5_14_18_1_4418 26 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 249 (accept_3_4 25 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 249 (accept_3_4 22 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 249 (accept_3_4 19 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 249 (accept_3_4 16 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 249 (accept_3_4 13 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 249 (accept_3_4 10 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 249 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 98 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 249
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 249 (accept_3_4 7 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  249 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 98 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 249 (accept_3_4 4 98 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 98
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 249 (accept_3_4 1 98 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  249 (allA_succ_of_accept 96 97 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 97 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 249 (accept_3_5 95 97 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 93
  97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 249 (accept_3_5 92 97
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 249 (Polychromatic418967fa.accept_9_1_7_6_1_75
  91 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 249
  (Polychromatic418967fa.accept_11_2_9_7_1_124 90 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 249 (accept_3_5 89 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 249 (accept_3_5 86 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 85 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 84 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 249 (accept_3_5 83 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 249 (Polychromatic418967fa.accept_17_13_12_11_1_2947 81 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 249 (accept_3_5 80 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 97 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 249
  (Polychromatic418967fa.accept_10_8_7_9_1_425 78 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 249 (accept_3_5 77 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 249 (accept_3_5 74 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 249 (accept_3_5 71 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 249 (Polychromatic418967fa.accept_13_4_6_2_1_1437 69 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 249 (accept_3_5 68 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 249 (accept_3_5 65 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 249 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 249 (accept_3_5 62 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 249
  (Polychromatic418967fa.accept_11_5_9_7_1_411 60 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 249 (accept_3_5 59 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 249 (accept_3_5 56 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 249 (accept_3_5 53 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 249 (accept_3_5 50 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 249 (accept_3_5 47 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 249 (accept_3_5 44 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 249 (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 249
  (Polychromatic418967fa.accept_10_2_7_9_1_783 42 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 249 (accept_3_5 41 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 249 (accept_3_5 38 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 249
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 249 (accept_3_5 35 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 249 (accept_3_5 32 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 249 (accept_3_5 29 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 249 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 249 (accept_3_5 26 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 249 (Polychromatic418967fa.accept_13_12_6_2_1_1441 25 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 249 (accept_3_5 23 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 249 (accept_3_5 20 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 249
  (Polychromatic418967fa.accept_10_8_7_9_1_425 18 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 249 (accept_3_5 17 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 249 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 249 (accept_3_5 14 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 249 (accept_3_5 11 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 249 (accept_3_5 8 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 249 (Polychromatic418967fa.accept_20_7_17_9_1_10825 7 97 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 249
  (Polychromatic418967fa.accept_17_6_12_11_1_5231 6 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 249 (accept_3_5 5 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 97 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 249 (accept_3_5 2 97 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 97 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 249
  (allA_succ_of_accept 95 96 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 95 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 249 (Polychromatic418967fa.accept_13_3_5_2_1_1475 94 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 96 249 3 31 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 96 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 92 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 96 249 (Polychromatic418967fa.accept_15_1_6_9_1_254 91 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 249 3 30 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 249 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  89 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 249
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 88 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 96 249 3 29 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 96 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 249 3 28 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 249 (Polychromatic418967fa.accept_13_4_5_2_1_1436 82 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 249 3 27 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 249
  (Polychromatic418967fa.accept_27_26_15_6_1_15040 80 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 96 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 96 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 249 3 26 32 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 249
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 77 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 96 249 3 25 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 96 249 (Polychromatic418967fa.accept_13_9_5_2_1_2185
  74 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 249
  (Polychromatic418967fa.accept_10_3_6_9_1_779 73 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 249 3 24 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 96 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 249 (Polychromatic418967fa.accept_11_4_8_7_1_819 70 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 96 249 3 23 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 96 249
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 68 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 96 249 (Polychromatic418967fa.accept_20_7_16_9_1_4970 67 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 249 3 22 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 65
  96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 64 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 96 249 3 21 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 96 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 249 (Polychromatic418967fa.accept_13_9_5_2_1_2185 61 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 249 3 20 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 249
  (Polychromatic418967fa.accept_11_4_8_7_1_819 59 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 96 249 3 19 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 96 249 (Polychromatic418967fa.accept_13_4_5_2_1_1436
  56 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 249 3 18 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 96 249 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 249 (Polychromatic418967fa.accept_18_16_6_15_1_3376 52 96
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 96 249 3 17 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 96 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 96 249 (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 249 3 16 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 249 (Polychromatic418967fa.accept_18_11_6_15_1_5953
  47 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 249
  (Polychromatic418967fa.accept_13_7_5_2_1_401 46 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 96 249 3 15 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 96 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 249 3 14 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 249 (Polychromatic418967fa.accept_18_4_6_15_1_2250 40 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 249 3 13 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 249 (Polychromatic418967fa.accept_13_12_5_2_1_2173
  38 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 249 3 12 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 96 249 3 11 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 96 249
  (Polychromatic418967fa.accept_19_13_1_2_1_11154 32 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 249 (Polychromatic418967fa.accept_15_1_6_9_1_254 31 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 249 3 10 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 249
  (Polychromatic418967fa.accept_18_10_6_15_1_3412 28 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 96 249 3 9 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 96 249 (Polychromatic418967fa.accept_11_4_8_7_1_819 26 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 249 3 8 32 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 249 3 7 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 249
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 249 3 6 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 249 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 249 3 5 32 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 249
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 249 3 4 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 249 (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 249
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 96 249 3 3 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 96 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 249 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 249 3 2 32 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 249
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 249 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 96 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 249 3 1 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 96 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 95 249 (allA_succ_of_accept 94 95 249 (accept_3_4 94 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 95 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 93 95 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 95 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 249 (accept_3_4 91 95 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 90
  95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 89 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 249 (accept_3_4 88 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 87 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 249 (accept_3_4 85 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 83 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 249 (accept_3_4 82 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 249 (accept_3_4 79 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 249
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 77 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 249 (accept_3_4 76 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 249 (accept_3_4 73 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 249 (Polychromatic418967fa.accept_15_12_5_9_1_3234 72 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 249 (accept_3_4 70 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 249 (Polychromatic418967fa.accept_17_1_10_11_1_2943 69 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 249 (accept_3_4 67 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 249 (accept_3_4 64 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 249 (accept_3_4 61 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 249 (Polychromatic418967fa.accept_18_6_5_15_1_7292 60 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 249
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 59 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 249 (accept_3_4 58 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 249 (accept_3_4 55 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 249 (accept_3_4 52 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 249 (accept_3_4 49 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 249 (accept_3_4 46 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 249 (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 249 (accept_3_4 43 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 249
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 249 (accept_3_4 40 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 249 (accept_3_4 37 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 249 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 249 (accept_3_4 34 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 249 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 249 (accept_3_4 31 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 249 (accept_3_4 28 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 249 (accept_3_4 25 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 249 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 249
  (Polychromatic418967fa.accept_20_3_15_9_1_6456 23 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 249 (accept_3_4 22 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 249 (accept_3_4 19 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 249 (accept_3_4 16 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 249 (accept_3_4 13 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 249 (accept_3_4 10 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 249 (Polychromatic418967fa.accept_18_9_5_15_1_2246 9 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 249 (accept_3_4 7 95 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 249
  (Polychromatic418967fa.accept_13_5_4_2_1_846 5 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 249 (accept_3_4 4 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  249 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 95 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 249 (accept_3_4 1 95 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 249
  (allA_succ_of_accept 93 94 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 93 94 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 249 (accept_3_5 92 94 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 90
  94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 249 (accept_3_5 89 94
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 249
  (Polychromatic418967fa.accept_9_7_4_6_1_273 88 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 249 (accept_3_5 86 94 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 84
  94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 249 (accept_3_5 83 94
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 249 (Polychromatic418967fa.accept_9_1_4_6_1_5
  82 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 249
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 81 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 249 (accept_3_5 80 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 249 (accept_3_5 77 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 249 (accept_3_5 74 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 249 (Polychromatic418967fa.accept_15_12_4_9_1_3204 72 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 249 (accept_3_5 71 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 94 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 249 (accept_3_5 68 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 249 (accept_3_5 65 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 249 (accept_3_5 62 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 249 (Polychromatic418967fa.accept_18_6_4_15_1_2276 60 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 249 (accept_3_5 59 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 94 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 249 (accept_3_5 56 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 249 (accept_3_5 53 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 249 (accept_3_5 50 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 249 (accept_3_5 47 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 249
  (Polychromatic418967fa.accept_10_5_4_9_1_420 45 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 249 (accept_3_5 44 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 249 (accept_3_5 41 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 249 (Polychromatic418967fa.accept_13_1_3_2_1_1429 40 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 249 (accept_3_5 38 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 249 (accept_3_5 35 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 249
  (Polychromatic418967fa.accept_10_3_4_9_1_15 33 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 249 (accept_3_5 32 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 249 (accept_3_5 29 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 249 (accept_3_5 26 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 249 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 249 (accept_3_5 23 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 249 (accept_3_5 20 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 249 (accept_3_5 17 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 249 (accept_3_5 14 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 249 (accept_3_5 11 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 94 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 249
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 249 (accept_3_5 8 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 94 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 249 (accept_3_5 5 94 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 249 (Polychromatic418967fa.accept_16_4_14_9_1_4657 4 94 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 249 (accept_3_5 2 94 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 249
  (allA_succ_of_accept 92 93 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 92 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 91 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 249 3 30 31 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 89 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 88 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 249 3 29 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 86
  93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 85 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 249 3 28 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 249 3 27 31 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 249 3 26 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 76 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 249 3 25 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 249 3 24 31 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 249 3 23 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 68
  93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 249 3 22 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 249 3 21 31 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 249 3 20 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 249 3 19 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 249 3 18 31 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 249 3 17 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 249 3 16 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 249 3 15 31 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 249 3 14 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 41
  93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 40 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 249 3 13 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 249 3 12 31 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 249 3 11 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 249 3 10 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 249 3 9 31 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 249 3 8 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 249 3 7 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 249 3 6 31 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 249 3 5 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 249 3 4 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 249 3 3 31 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 249 3 2 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 93 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 249 3 1 31 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 93 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 249
  (allA_succ_of_accept 91 92 249 (accept_3_4 91 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 90 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 249 (accept_3_4 88 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 86 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 249 (accept_3_4 85 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 249 (accept_3_4 82 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 249 (Polychromatic418967fa.accept_10_1_2_9_1_152 81 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 249 (accept_3_4 79 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 78 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 249 (accept_3_4 76 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 249
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 74 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 249 (accept_3_4 73 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 249 (Polychromatic418967fa.accept_16_8_12_9_1_2569 72 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 249 (accept_3_4 70 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 249 (accept_3_4 67 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 249 (accept_3_4 64 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 249 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 249 (accept_3_4 61 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 249 (Polychromatic418967fa.accept_14_4_8_11_1_794 60 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 249 (accept_3_4 58 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 249
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 56 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 249 (accept_3_4 55 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 249 (accept_3_4 52 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 249 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 249 (accept_3_4 49 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 249 (accept_3_4 46 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 249 (accept_3_4 43 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 249 (accept_3_4 40 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 249 (accept_3_4 37 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 249 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 249 (accept_3_4 34 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 249 (accept_3_4 31 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 249 (accept_3_4 28 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 249 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 249 (accept_3_4 25 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 249 (accept_3_4 22 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 249
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 20 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 249 (accept_3_4 19 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 249 (accept_3_4 16 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 249 (Polychromatic418967fa.accept_21_15_8_18_1_10689 15 92 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 249 (accept_3_4 13 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 249 (accept_3_4 10 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 249 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 92 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 249 (accept_3_4 7 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  249 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 249 (accept_3_4 4 92 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 92 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 249 (Polychromatic418967fa.accept_16_2_12_9_1_2568
  2 92 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 249 (accept_3_4 1 92
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 249
  (allA_succ_of_accept 90 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 249 (accept_3_5 89 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 249 (Polychromatic418967fa.accept_11_10_3_7_1_2564
  87 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 249 (accept_3_5 86
  91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 249
  (Polychromatic418967fa.accept_9_4_1_6_1_284 85 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 249 (accept_3_5 83 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 249 (Polychromatic418967fa.accept_11_4_3_7_1_828
  81 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 249 (accept_3_5 80
  91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 249
  (Polychromatic418967fa.accept_9_7_1_6_1_261 79 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 249 (accept_3_5 77 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 91 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 75
  91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 249 (accept_3_5 74 91
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 249
  (Polychromatic418967fa.accept_14_3_7_11_1_765 73 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 91 249 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 249 (accept_3_5 71 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 249 (Polychromatic418967fa.accept_16_5_11_9_1_861
  69 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 249 (accept_3_5 68
  91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 249
  (Polychromatic418967fa.accept_9_4_1_6_1_284 67 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 249 (accept_3_5 65 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 91 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  63 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 249 (accept_3_5 62
  91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 249
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 91 249 (Polychromatic418967fa.accept_14_4_7_11_1_790 60 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 249 (accept_3_5 59 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 57
  91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 249 (accept_3_5 56 91
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 249
  (Polychromatic418967fa.accept_10_5_1_9_1_791 55 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 249 (accept_3_5 53 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 91 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  51 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 249 (accept_3_5 50
  91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 249
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 91 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 249 (accept_3_5 47 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 249 (Polychromatic418967fa.accept_10_5_1_9_1_791
  45 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 249 (accept_3_5 44
  91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 249
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 249 (accept_3_5 41 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 91 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 39
  91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 249 (accept_3_5 38 91
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 249
  (Polychromatic418967fa.accept_11_4_3_7_1_828 37 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 91 249 (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 249 (accept_3_5 35 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 249
  (Polychromatic418967fa.accept_21_12_7_18_1_7683 33 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 249 (accept_3_5 32 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 249 (accept_3_5 29 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 249
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 249 (accept_3_5 26 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 249 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 91 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 249 (accept_3_5 23 91 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 249 (accept_3_5 20 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 249 (Polychromatic418967fa.accept_21_19_7_18_1_7686 19 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 249 (accept_3_5 17 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 249
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 249 (accept_3_5 14 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 249 (accept_3_5 11 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 249
  (Polychromatic418967fa.accept_19_9_15_2_1_9758 9 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 249 (accept_3_5 8 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  249 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 249 (accept_3_5 5 91 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 249 (accept_3_5 2 91 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 249 (Polychromatic418967fa.accept_19_1_15_2_1_6950
  1 91 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 249
  (allA_succ_of_accept 89 90 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 89 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 88 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 249 3 29 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 86 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 90 249 (Polychromatic418967fa.accept_20_5_10_9_1_9485 85 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 249 3 28 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 83
  90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 82 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 90 249 3 27 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 90 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 249 3 26 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 249
  (Polychromatic418967fa.accept_19_1_14_2_1_4134 77 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 249 3 25 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 249 (Polychromatic418967fa.accept_12_2_6_9_1_19 74
  90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 249 3 24 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 70 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 90 249 3 23 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 249 3 22 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 65
  90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 249
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 64 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 90 249 3 21 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 90 249 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 249 3 20 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 249 3 19 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 249 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  56 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 249 3 18 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 249 (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 90 249 3 17 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 90 249
  (Polychromatic418967fa.accept_12_2_6_9_1_19 50 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 249 (Polychromatic418967fa.accept_13_10_12_2_1_1460 49 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 249 3 16 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 249
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 249 3 15 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 249 3 14 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 249
  (Polychromatic418967fa.accept_17_7_5_11_1_2922 41 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 249 3 13 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 249 3 12 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 249 3 11 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 249
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 249 3 10 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 249 (Polychromatic418967fa.accept_13_3_12_2_1_385
  29 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 249
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 249 3 9 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 249 (Polychromatic418967fa.accept_20_5_10_9_1_9485 25 90
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 249 3 8 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 249 3 7 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 249 (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 249 3 6 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 249 3 5 30 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 249
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 249 (Polychromatic418967fa.accept_20_13_10_9_1_5030 13 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 249 3 4 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 249 3 3 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 249 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 249 3 2 30 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 90 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 249 3 1 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 90 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 249
  (Polychromatic418967fa.accept_13_1_12_2_1_384 1 90 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 249 (allA_succ_of_accept 88 89 249 (accept_3_4 88 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 87 89 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 89 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 249 (accept_3_4 85 89 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 84
  89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 249 (accept_3_4 82 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 249 (Polychromatic418967fa.accept_13_3_11_2_1_1422 81 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 249 (accept_3_4 79 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 249 (accept_3_4 76 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 249 (accept_3_4 73 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 249 (accept_3_4 70 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 249 (accept_3_4 67 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 249 (accept_3_4 64 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 249 (accept_3_4 61 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 249 (Polychromatic418967fa.accept_18_6_17_15_1_4603 60 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 249 (accept_3_4 58 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 249 (accept_3_4 55 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 249 (Polychromatic418967fa.accept_19_16_13_2_1_6920 54 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 249
  (Polychromatic418967fa.accept_15_8_14_9_1_4216 53 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 249 (accept_3_4 52 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 249 (accept_3_4 49 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 249 (accept_3_4 46 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 249 (Polychromatic418967fa.accept_18_9_17_15_1_2267 45 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 249 (accept_3_4 43 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 249 (Polychromatic418967fa.accept_13_3_11_2_1_1422 42 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 249 (accept_3_4 40 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 249 (accept_3_4 37 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 249
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 249 (accept_3_4 34 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 249 (Polychromatic418967fa.accept_21_12_5_18_1_7715 33 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 249 (accept_3_4 31 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 249 (accept_3_4 28 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 249 (accept_3_4 25 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 249 (Polychromatic418967fa.accept_18_6_17_15_1_4603 24 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 249 (accept_3_4 22 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 249 (accept_3_4 19 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 249 (Polychromatic418967fa.accept_22_18_1_7_1_15039 18 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 249
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 249 (accept_3_4 16 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 249 (accept_3_4 13 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 249 (accept_3_4 10 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 249 (accept_3_4 7 89 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 89 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 249 (accept_3_4 4 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  249 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 89 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 249 (accept_3_4 1 89 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 249 (allA_succ_of_accept 87 88 249 (Polychromatic418967fa.accept_10_7_8_9_1_785 87 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 249 (accept_3_5 86 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 84 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 88 249 (accept_3_5 83 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  88 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 82 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 88 249 (Polychromatic418967fa.accept_10_1_8_9_1_787 81 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 249 (accept_3_5 80 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 249
  (Polychromatic418967fa.accept_12_6_4_9_1_544 78 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 249 (accept_3_5 77 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 76 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 249 (accept_3_5 74 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 249
  (Polychromatic418967fa.accept_21_9_4_18_1_7615 72 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 249 (accept_3_5 71 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 249 (Polychromatic418967fa.accept_13_5_10_2_1_856 70 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 249 (Polychromatic418967fa.accept_21_6_4_18_1_9164 69 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 249 (accept_3_5 68 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 249 (accept_3_5 65 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 249 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 249 (accept_3_5 62 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 249
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 249 (accept_3_5 59 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 249 (accept_3_5 56 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 249
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 249 (accept_3_5 53 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 249 (Polychromatic418967fa.accept_15_7_13_9_1_1466 52 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 249 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 249 (accept_3_5 50 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 249 (accept_3_5 47 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 249 (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 249 (accept_3_5 44 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 249
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 249 (accept_3_5 41 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 249 (accept_3_5 38 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 249
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 249 (accept_3_5 35 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 249 (Polychromatic418967fa.accept_15_3_13_9_1_3196 33 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 249 (accept_3_5 32 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 249 (accept_3_5 29 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 249 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 249 (accept_3_5 26 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 249
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 249 (accept_3_5 23 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 249 (accept_3_5 20 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 249
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 249 (accept_3_5 17 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 249 (Polychromatic418967fa.accept_13_3_10_2_1_381 16 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 249 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 249 (accept_3_5 14 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 249 (accept_3_5 11 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 249 (Polychromatic418967fa.accept_17_9_3_11_1_3983 9 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 249 (accept_3_5 8 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 249
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 249 (accept_3_5 5 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  249 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 88 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 249 (accept_3_5 2 88 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 249
  (allA_succ_of_accept 86 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 249 3 28 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 83 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 249 3 27 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 249 (Polychromatic418967fa.accept_11_3_10_7_1_129
  80 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 79 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 249 3 26 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 249 3 25 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 249 3 24 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 71
  87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 249 3 23 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 249 (Polychromatic418967fa.accept_10_8_7_9_1_425 68 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 67 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 249 3 22 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 249
  (Polychromatic418967fa.accept_12_5_3_9_1_541 65 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 249 3 21 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 61 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 249 3 20 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 249 3 19 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 249
  (Polychromatic418967fa.accept_16_8_7_9_1_7052 56 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 249 3 18 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 53
  87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 249
  (Polychromatic418967fa.accept_10_2_7_9_1_783 52 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 249 3 17 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 249 3 16 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 249
  (Polychromatic418967fa.accept_11_3_10_7_1_129 47 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 249 3 15 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 249 (Polychromatic418967fa.accept_13_5_9_2_1_1489
  44 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 249 3 14 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 249 (Polychromatic418967fa.accept_13_1_9_2_1_1448 40 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 249 3 13 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 249 3 12 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 249 3 11 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 249 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 249 3 10 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 249 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 249 3 9 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 249
  (Polychromatic418967fa.accept_11_3_10_7_1_129 25 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 249 3 8 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 249 3 7 29 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 249 3 6 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 249
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 16 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 249 3 5 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 249 3 4 29 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 249
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 249 3 3 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 249 3 2 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 249 (Polychromatic418967fa.accept_15_4_12_9_1_773 4 87 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 249 3 1 29 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 87 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 249
  (allA_succ_of_accept 85 86 249 (accept_3_4 85 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 249 (accept_3_4 82 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 249 (Polychromatic418967fa.accept_15_6_11_9_1_3215 81 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 80 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 249 (accept_3_4 79 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 249 (accept_3_4 76 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 74 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 249 (accept_3_4 73 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 249 (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 249 (accept_3_4 70 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 249 (accept_3_4 67 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 249 (accept_3_4 64 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 249 (accept_3_4 61 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 249 (Polychromatic418967fa.accept_11_5_9_7_1_411 60 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 249 (accept_3_4 58 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 249 (accept_3_4 55 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 249 (accept_3_4 52 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 249
  (Polychromatic418967fa.accept_15_5_11_9_1_4276 50 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 249 (accept_3_4 49 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 249 (accept_3_4 46 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 249 (accept_3_4 43 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 249 (accept_3_4 40 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 249 (accept_3_4 37 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 249 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 249 (accept_3_4 34 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 249
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 32 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 249 (accept_3_4 31 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 249 (accept_3_4 28 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 249 (accept_3_4 25 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 249 (Polychromatic418967fa.accept_11_2_9_7_1_124 24 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 249 (accept_3_4 22 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 249 (accept_3_4 19 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 249 (accept_3_4 16 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 249
  (Polychromatic418967fa.accept_20_14_6_9_1_9460 14 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 249 (accept_3_4 13 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 249 (accept_3_4 10 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 249 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 86 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 249 (accept_3_4 7 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  249 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 249 (accept_3_4 4 86 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 249 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  86 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 249 (accept_3_4 1 86 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 249
  (allA_succ_of_accept 84 85 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 85 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 249 (accept_3_5 83 85 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 249 (Polychromatic418967fa.accept_10_1_5_9_1_157
  81 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 249 (accept_3_5 80
  85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 249
  (Polychromatic418967fa.accept_9_7_4_6_1_273 79 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 249 (Polychromatic418967fa.accept_15_3_10_9_1_769 78 85 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 249 (accept_3_5 77 85 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 75
  85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 249 (accept_3_5 74 85
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 249 (Polychromatic418967fa.accept_15_12_10_9_1_798 72 85 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 249 (accept_3_5 71 85 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 249
  (Polychromatic418967fa.accept_19_12_9_2_1_11136 69 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 85 249 (accept_3_5 68 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  85 249 (Polychromatic418967fa.accept_20_7_5_9_1_10833 67 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 85 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 249 (accept_3_5 65 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 249
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 249 (accept_3_5 62 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 85 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 249 (accept_3_5 59 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 249 (accept_3_5 56 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 249 (accept_3_5 53 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 249
  (Polychromatic418967fa.accept_10_1_5_9_1_157 51 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 249 (accept_3_5 50 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 249 (Polychromatic418967fa.accept_15_4_10_9_1_4298 49 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 249 (accept_3_5 47 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 249 (accept_3_5 44 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 249 (Polychromatic418967fa.accept_15_12_10_9_1_798 42 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 249 (accept_3_5 41 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 249 (accept_3_5 38 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 249 (accept_3_5 35 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 249 (accept_3_5 32 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 249 (accept_3_5 29 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 249
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 249 (accept_3_5 26 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 249 (accept_3_5 23 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 249 (accept_3_5 20 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 249 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 249 (accept_3_5 17 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 249
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 249 (accept_3_5 14 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 249 (Polychromatic418967fa.accept_16_13_5_9_1_4682 13 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 249 (accept_3_5 11 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 85 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 249
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 249 (accept_3_5 8 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  249 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 249 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 85 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 249 (accept_3_5 5 85 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  85 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 249 (accept_3_5 2 85 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 249
  (allA_succ_of_accept 83 84 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 249 3 27 28 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 249 3 26 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 77
  84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 84 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 84 249 3 25 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 84 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 249 3 24 28 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 249 3 23 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 249 3 22 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 249 3 21 28 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 84 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 249 3 20 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 84 249 3 19 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 84 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 249 3 18 28 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 249
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 249 3 17 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 249 3 16 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 249 3 15 28 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 249 3 14 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 84 249 3 13 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 84 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 249 3 12 28 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 249 3 11 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 249 3 10 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 249 3 9 28 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 249 3 8 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 249 3 7 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 249 3 6 28 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 249 3 5 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 249
  (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 249 3 4 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 249 3 3 28 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 249 3 2 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 84 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 84 249 3 1 28 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 84 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 84 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 249
  (allA_succ_of_accept 82 83 249 (accept_3_4 82 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 249 (Polychromatic418967fa.accept_13_3_5_2_1_1475 81 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 249 (accept_3_4 79 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 77 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 249 (accept_3_4 76 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 249 (accept_3_4 73 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 71 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 249 (accept_3_4 70 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 249 (Polychromatic418967fa.accept_13_4_5_2_1_1436 69 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 249 (accept_3_4 67 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 249 (accept_3_4 64 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 249 (accept_3_4 61 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 249 (Polychromatic418967fa.accept_16_12_3_9_1_5886 60 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 249 (accept_3_4 58 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 249 (accept_3_4 55 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 249 (accept_3_4 52 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 249 (accept_3_4 49 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 249 (accept_3_4 46 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 249 (accept_3_4 43 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 249 (accept_3_4 40 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 249 (accept_3_4 37 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 249 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 249 (accept_3_4 34 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 249 (accept_3_4 31 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 249
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 249 (accept_3_4 28 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 249 (accept_3_4 25 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 249 (accept_3_4 22 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 249 (accept_3_4 19 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 249 (accept_3_4 16 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 249 (accept_3_4 13 83 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 249
  (Polychromatic418967fa.accept_21_11_20_18_1_7656 11 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 83 249 (accept_3_4 10 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 83 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 83 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 249 (accept_3_4 7 83 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 249 (accept_3_4 4 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  249 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 249 (accept_3_4 1 83 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 249 (allA_succ_of_accept 81 82 249 (Polychromatic418967fa.accept_10_1_2_9_1_152 81 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 249 (accept_3_5 80 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 78 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 82 249 (accept_3_5 77 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  82 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 249 (accept_3_5 74 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 82 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 249 (accept_3_5 71 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 249 (accept_3_5 68 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 249 (accept_3_5 65 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 249 (accept_3_5 62 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 249
  (Polychromatic418967fa.accept_16_12_2_9_1_3461 60 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 249 (accept_3_5 59 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 249 (accept_3_5 56 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 249
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 249 (accept_3_5 53 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 249 (accept_3_5 50 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 249 (accept_3_5 47 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 249 (Polychromatic418967fa.accept_15_1_7_9_1_20 46 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 249 (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 249 (accept_3_5 44 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 249
  (Polychromatic418967fa.accept_11_9_5_7_1_815 42 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 249 (accept_3_5 41 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 249 (accept_3_5 38 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 249 (accept_3_5 35 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 249 (Polychromatic418967fa.accept_16_1_2_9_1_1607 33 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 249 (accept_3_5 32 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 249 (accept_3_5 29 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 249 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 249 (accept_3_5 26 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 249
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 249 (accept_3_5 23 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 249 (accept_3_5 20 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 249
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 249 (accept_3_5 17 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 249 (accept_3_5 14 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 249 (accept_3_5 11 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 249 (Polychromatic418967fa.accept_19_10_6_2_1_6907 10 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 249 (accept_3_5 8 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 249 (accept_3_5 5 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  249 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 82 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 249 (accept_3_5 2 82 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 249
  (allA_succ_of_accept 80 81 249 (Polychromatic418967fa.accept_11_3_4_7_1_114 80 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 249 (Polychromatic418967fa.accept_13_1_3_2_1_1429 79 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 249 3 26 27 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 249
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 77 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 249 (Polychromatic418967fa.accept_13_11_3_2_1_863 76 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 249 3 25 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 249 (Polychromatic418967fa.accept_11_8_4_7_1_1303
  74 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 249
  (Polychromatic418967fa.accept_19_16_5_2_1_8375 73 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 249 3 24 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 249 (Polychromatic418967fa.accept_15_11_6_9_1_3236 71 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 249 (Polychromatic418967fa.accept_13_5_3_2_1_1499 70 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 249 3 23 27 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 249
  (Polychromatic418967fa.accept_10_8_1_9_1_413 68 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 249 (Polychromatic418967fa.accept_19_10_5_2_1_9784 67 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 249 3 22 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 249 (Polychromatic418967fa.accept_10_5_1_9_1_791 65
  81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 249
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 64 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 249 3 21 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 249 (Polychromatic418967fa.accept_10_2_1_9_1_1248 62 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 249 (Polychromatic418967fa.accept_13_9_3_2_1_399 61 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 249 3 20 27 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 249
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 59 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 249 (Polychromatic418967fa.accept_10_8_1_9_1_413 58 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 249 3 19 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 249 (Polychromatic418967fa.accept_15_11_6_9_1_3236
  56 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 249
  (Polychromatic418967fa.accept_10_5_1_9_1_791 55 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 249 3 18 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 249 (Polychromatic418967fa.accept_13_1_3_2_1_1429 53 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 249 (Polychromatic418967fa.accept_10_2_1_9_1_1248 52 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 249 3 17 27 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 249
  (Polychromatic418967fa.accept_13_11_3_2_1_863 50 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 249 (Polychromatic418967fa.accept_13_10_3_2_1_4728 49 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 249 3 16 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 249 (Polychromatic418967fa.accept_11_3_4_7_1_114 47
  81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 249
  (Polychromatic418967fa.accept_15_1_6_9_1_254 46 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 249 3 15 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 249 (Polychromatic418967fa.accept_13_5_3_2_1_1499 44 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 249 (Polychromatic418967fa.accept_25_18_6_24_1_15038 43 81
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 249 3 14 27 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 249
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 249 (Polychromatic418967fa.accept_13_1_3_2_1_1429 40 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 249 3 13 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 249 (Polychromatic418967fa.accept_10_8_1_9_1_413 38
  81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 249
  (Polychromatic418967fa.accept_13_11_3_2_1_863 37 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 249 3 12 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 249 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 249 (Polychromatic418967fa.accept_15_4_6_9_1_2269 34 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 249 3 11 27 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 249
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 249 (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 249 3 10 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 249 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  29 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 249
  (Polychromatic418967fa.accept_10_8_1_9_1_413 28 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 249 3 9 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 249 (Polychromatic418967fa.accept_15_11_6_9_1_3236 26 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 249 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 249 3 8 27 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 249
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 249 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 249 3 7 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 249 (Polychromatic418967fa.accept_22_20_15_7_1_15037 20 81
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 249
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 249 3 6 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 249 (Polychromatic418967fa.accept_18_17_9_15_1_7268 17 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 249 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 249 3 5 27 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 249
  (Polychromatic418967fa.accept_11_3_4_7_1_114 14 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 249 (Polychromatic418967fa.accept_16_13_1_9_1_2597 13 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 249 3 4 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 249 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 249
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 10 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 249 3 3 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 249 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 249 (Polychromatic418967fa.accept_17_7_13_11_1_2895 7 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 249 3 2 27 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 249
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 249 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 81 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 249 3 1 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 249 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 81 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 249
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 81 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 249
  (allA_succ_of_accept 79 80 249 (accept_3_4 79 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 249 (accept_3_4 76 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 249 (accept_3_4 73 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 249 (Polychromatic418967fa.accept_15_12_5_9_1_3234 72 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 249 (accept_3_4 70 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 249 (accept_3_4 67 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 249 (accept_3_4 64 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 249 (Polychromatic418967fa.accept_14_7_10_11_1_8112 63 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 249 (accept_3_4 61 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 249 (Polychromatic418967fa.accept_22_16_14_7_1_13581 60 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 249 (accept_3_4 58 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 249 (accept_3_4 55 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 249 (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 249 (accept_3_4 52 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 249 (Polychromatic418967fa.accept_21_9_17_18_1_3009 51 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 249 (accept_3_4 49 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 249 (accept_3_4 46 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 249 (Polychromatic418967fa.accept_19_7_4_2_1_6959 45 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 249
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 44 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 249 (accept_3_4 43 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 249 (accept_3_4 40 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 249 (accept_3_4 37 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 249 (accept_3_4 34 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 249 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 249 (accept_3_4 31 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 249 (accept_3_4 28 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 249
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 249 (accept_3_4 25 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 249 (Polychromatic418967fa.accept_19_5_4_2_1_6840 24 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 249 (accept_3_4 22 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 249 (accept_3_4 19 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 249 (accept_3_4 16 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 249 (accept_3_4 13 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 249 (accept_3_4 10 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 249 (Polychromatic418967fa.accept_19_9_4_2_1_9753 9 80 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 249 (accept_3_4 7 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  249 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 80 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 249 (accept_3_4 4 80 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 80
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 249 (accept_3_4 1 80 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 249
  (allA_succ_of_accept 78 79 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 249 (accept_3_5 77 79 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 75
  79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 249 (accept_3_5 74 79
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 249 (Polychromatic418967fa.accept_9_1_7_6_1_75
  73 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 249
  (Polychromatic418967fa.accept_14_2_9_11_1_3054 72 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 249 (accept_3_5 71 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 249 (accept_3_5 68 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 249 (accept_3_5 65 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 249 (accept_3_5 62 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 249
  (Polychromatic418967fa.accept_22_16_13_7_1_5520 60 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 249 (accept_3_5 59 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 249 (accept_3_5 56 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 249 (accept_3_5 53 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 249 (accept_3_5 50 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 249 (accept_3_5 47 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 249 (Polychromatic418967fa.accept_13_6_1_2_1_1464 45 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 249 (accept_3_5 44 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 249 (Polychromatic418967fa.accept_15_13_4_9_1_2283 43 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 249 (accept_3_5 41 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 249 (accept_3_5 38 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 249
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 249 (accept_3_5 35 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 249 (accept_3_5 32 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 249 (accept_3_5 29 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 249 (accept_3_5 26 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 249 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 249
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 24 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 249 (accept_3_5 23 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 249 (accept_3_5 20 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 249 (accept_3_5 17 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 249 (accept_3_5 14 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 249 (accept_3_5 11 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 249 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 249 (accept_3_5 8 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 249 (Polychromatic418967fa.accept_25_7_4_24_1_15036 7 79 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 249 (accept_3_5 5 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 79 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 249 (accept_3_5 2 79 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 79 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 249
  (allA_succ_of_accept 77 78 249 (Polychromatic418967fa.accept_10_7_8_9_1_785 77 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 249 3 25 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 249
  (Polychromatic418967fa.accept_10_4_8_9_1_784 74 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 249 3 24 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 249
  (Polychromatic418967fa.accept_12_10_6_9_1_549 70 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 249 3 23 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 249 3 22 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 249
  (Polychromatic418967fa.accept_15_5_3_9_1_283 65 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 249 3 21 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 249 (Polychromatic418967fa.accept_12_2_6_9_1_19 62
  78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 249 3 20 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 249 3 19 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 249
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 249 3 18 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 249 (Polychromatic418967fa.accept_15_8_3_9_1_4220
  53 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 52 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 249 3 17 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 249 (Polychromatic418967fa.accept_11_6_1_7_1_1315 50 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 249 (Polychromatic418967fa.accept_21_7_15_18_1_7526 49 78
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 249 3 16 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 249 3 15 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 44
  78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 249 3 14 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 249 (Polychromatic418967fa.accept_10_1_8_9_1_787 41 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 249 3 13 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 249 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 249 3 12 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 249
  (Polychromatic418967fa.accept_10_4_8_9_1_784 34 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 249 3 11 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 249 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 249 3 10 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 249
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 29 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 249 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 249 3 9 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 249
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 249 3 8 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 249 3 7 26 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 249
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 249 3 6 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 249
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 249 3 5 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 249 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 78
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 249 3 4 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 249 3 3 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 249 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 249 3 2 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 78 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 249 3 1 26 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 249
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 78 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 249 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 78 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 249
  (allA_succ_of_accept 76 77 249 (accept_3_4 76 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 249 (accept_3_4 73 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 249 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 249 (accept_3_4 70 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 249 (Polychromatic418967fa.accept_13_4_12_2_1_1459 69 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 249 (accept_3_4 67 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 249 (accept_3_4 64 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 249 (accept_3_4 61 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 249
  (Polychromatic418967fa.accept_14_3_7_11_1_765 59 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 249 (accept_3_4 58 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 249 (accept_3_4 55 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 249 (Polychromatic418967fa.accept_16_6_13_9_1_4690 54 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 249 (accept_3_4 52 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 249 (accept_3_4 49 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 249 (accept_3_4 46 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 249 (Polychromatic418967fa.accept_13_6_12_2_1_4707 45 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 249 (accept_3_4 43 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 249 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 249
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 41 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 249 (accept_3_4 40 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 249 (accept_3_4 37 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 249 (accept_3_4 34 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 249 (Polychromatic418967fa.accept_16_1_13_9_1_2551 33 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 249 (accept_3_4 31 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 249 (accept_3_4 28 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 249 (accept_3_4 25 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 249 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 249
  (Polychromatic418967fa.accept_13_10_12_2_1_1460 23 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 249 (accept_3_4 22 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 249 (accept_3_4 19 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 249 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 249 (accept_3_4 16 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 249 (accept_3_4 13 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 249 (accept_3_4 10 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 249 (Polychromatic418967fa.accept_18_9_5_15_1_2246 9 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 249 (accept_3_4 7 77 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 249 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 77 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 249
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 249 (accept_3_4 4 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  249 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 249 (accept_3_4 1 77 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 249 (allA_succ_of_accept 75 76 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 249 (accept_3_5 74 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 249 (accept_3_5 71 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 249 (accept_3_5 68 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 249 (accept_3_5 65 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 249 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 249 (accept_3_5 62 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 249
  (Polychromatic418967fa.accept_17_9_8_11_1_1040 60 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 249 (accept_3_5 59 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 249 (accept_3_5 56 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 249 (accept_3_5 53 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 249 (accept_3_5 50 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 249 (accept_3_5 47 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 249 (accept_3_5 44 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 249
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 249 (accept_3_5 41 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 249 (accept_3_5 38 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 249
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 249 (accept_3_5 35 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 249 (accept_3_5 32 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 249 (accept_3_5 29 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 249 (Polychromatic418967fa.accept_18_9_4_15_1_555 27 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 249 (accept_3_5 26 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 249 (accept_3_5 23 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 249 (Polychromatic418967fa.accept_13_9_11_2_1_1491 22 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 249 (accept_3_5 20 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 249
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 249 (accept_3_5 17 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 249 (accept_3_5 14 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 249 (accept_3_5 11 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 249 (accept_3_5 8 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 249
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 249 (accept_3_5 5 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  249 (Polychromatic418967fa.accept_13_4_11_2_1_1458 4 76 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 249 (accept_3_5 2 76 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 249 (allA_succ_of_accept
  74 75 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 75 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 249 3 24 25 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 249 3 23 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 249 3 22 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 249 3 21 25 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 249 3 20 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 249 3 19 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 249 3 18 25 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 249 3 17 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 249 3 16 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 249 3 15 25 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 249 3 14 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 249 3 13 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 249 3 12 25 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 249 3 11 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 249 3 10 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 249 3 9 25 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 249 3 8 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 249 3 7 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 249 3 6 25 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 249 3 5 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 249 3 4 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 249 3 3 25 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 249 3 2 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 75 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 249 3 1 25 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 75 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 249 (allA_succ_of_accept
  73 74 249 (accept_3_4 73 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 249
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 72 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 249 (accept_3_4 70 74 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 249 (Polychromatic418967fa.accept_19_12_17_2_1_6888 69 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 68 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 249 (accept_3_4 67 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 249 (accept_3_4 64 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 249 (accept_3_4 61 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 249 (Polychromatic418967fa.accept_19_3_17_2_1_6963 60 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 249 (accept_3_4 58 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 249
  (Polychromatic418967fa.accept_17_5_6_11_1_3974 56 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 249 (accept_3_4 55 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 249 (accept_3_4 52 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 249 (accept_3_4 49 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 249 (accept_3_4 46 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 249 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 249 (accept_3_4 43 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 249 (accept_3_4 40 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 249
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 249 (accept_3_4 37 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 249 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 249 (accept_3_4 34 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 249 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 249 (accept_3_4 31 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 249 (accept_3_4 28 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 249 (accept_3_4 25 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 249 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 249 (accept_3_4 22 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 249
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 20 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 249 (accept_3_4 19 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 249 (accept_3_4 16 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 249 (accept_3_4 13 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 249 (accept_3_4 10 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 249 (Polychromatic418967fa.accept_19_9_17_2_1_5428 9 74 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 249 (accept_3_4 7 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  249 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 249 (accept_3_4 4 74 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 249
  (Polychromatic418967fa.accept_26_2_22_15_1_15035 2 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 74 249 (accept_3_4 1 74 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 249 (allA_succ_of_accept
  72 73 249 (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 249 (accept_3_5 71 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 73 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 73 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 249 (accept_3_5 68 73 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 67
  73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 249 (accept_3_5 65 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 249 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 249 (accept_3_5 62 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 249
  (Polychromatic418967fa.accept_19_3_16_2_1_6837 60 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 249 (accept_3_5 59 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 249 (accept_3_5 56 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 249
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 249 (accept_3_5 53 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 249 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 249 (accept_3_5 50 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 249 (accept_3_5 47 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 249 (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 249 (accept_3_5 44 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 249
  (Polychromatic418967fa.accept_19_4_16_2_1_6967 42 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 249 (accept_3_5 41 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 249 (accept_3_5 38 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 249 (Polychromatic418967fa.accept_15_7_13_9_1_1466 37 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 249 (accept_3_5 35 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 249 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 249 (accept_3_5 32 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 249 (accept_3_5 29 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 249 (accept_3_5 26 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 249
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 249 (accept_3_5 23 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 249 (accept_3_5 20 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 249 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 249
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 18 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 249 (accept_3_5 17 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 249 (accept_3_5 14 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 249 (accept_3_5 11 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 249 (Polychromatic418967fa.accept_21_9_10_18_1_7567 9 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 249 (accept_3_5 8 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 249 (accept_3_5 5 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 249 (accept_3_5 2 73 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 249 (allA_succ_of_accept 71
  72 249 (Polychromatic418967fa.accept_10_1_2_9_1_152 71 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 249 (Polychromatic418967fa.accept_13_5_7_2_1_852 70 72 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 249 3 23 24 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 249 (Polychromatic418967fa.accept_10_7_2_9_1_775 67 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 249 3 22 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 249 (Polychromatic418967fa.accept_14_9_2_11_1_780
  65 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 249
  (Polychromatic418967fa.accept_15_4_12_9_1_773 64 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 249 3 21 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 72 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 249 3 20 24 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 249
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 59 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 249 (Polychromatic418967fa.accept_19_1_15_2_1_6950 58 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 249 3 19 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 249 (Polychromatic418967fa.accept_11_1_6_7_1_116 56
  72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 249 3 18 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 249 (Polychromatic418967fa.accept_21_11_9_18_1_4429 53 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 249 (Polychromatic418967fa.accept_16_4_8_9_1_4639 52 72 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 249 3 17 24 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 249
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 50 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 249 (Polychromatic418967fa.accept_15_4_12_9_1_773 49 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 249 3 16 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 47
  72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 249
  (Polychromatic418967fa.accept_19_8_15_2_1_6961 46 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 249 3 15 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 249 (Polychromatic418967fa.accept_13_5_7_2_1_852 44 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 249 (Polychromatic418967fa.accept_20_3_12_9_1_6410 43 72
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 249 3 14 24 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 249 3 13 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 249 (Polychromatic418967fa.accept_21_17_9_18_1_7521
  38 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 249
  (Polychromatic418967fa.accept_10_7_2_9_1_775 37 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 249 3 12 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 249 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 72 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 249 3 11 24 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 249
  (Polychromatic418967fa.accept_17_15_4_11_1_6515 32 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 249 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 249 3 10 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 249 (Polychromatic418967fa.accept_15_14_12_9_1_3216
  29 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 249
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 28 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 249 3 9 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 249 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 72
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 249 3 8 24 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 249
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 249 (Polychromatic418967fa.accept_13_9_7_2_1_3869 22 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 249 3 7 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 72 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 249 3 6 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 249 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 249 (Polychromatic418967fa.accept_23_16_3_19_1_15034 16 72
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 249 3 5 24 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 249
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 249 3 4 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 249 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 72 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 249
  (Polychromatic418967fa.accept_15_10_12_9_1_776 10 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 249 3 3 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 249 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 249 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 72 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 249 3 2 24 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 249 (Polychromatic418967fa.accept_15_4_12_9_1_773 4 72 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 249 3 1 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 249 (Polychromatic418967fa.accept_20_2_12_9_1_6435 2 72 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 249
  (Polychromatic418967fa.accept_10_1_2_9_1_152 1 72 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 249
  (allA_succ_of_accept 70 71 249 (accept_3_4 70 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 249 (Polychromatic418967fa.accept_13_4_6_2_1_1437 69 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 249 (accept_3_4 67 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 249 (accept_3_4 64 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 249 (accept_3_4 61 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 249 (Polychromatic418967fa.accept_13_8_6_2_1_865 60 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 249 (accept_3_4 58 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 249 (accept_3_4 55 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 249
  (Polychromatic418967fa.accept_11_9_5_7_1_815 53 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 249 (accept_3_4 52 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 249 (accept_3_4 49 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 249 (accept_3_4 46 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 249 (accept_3_4 43 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 249 (accept_3_4 40 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 249 (accept_3_4 37 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 249 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 249
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 249 (accept_3_4 34 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 249 (accept_3_4 31 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 249 (accept_3_4 28 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 249 (accept_3_4 25 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 249 (accept_3_4 22 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 249 (accept_3_4 19 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 249 (accept_3_4 16 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 249 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 249 (accept_3_4 13 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 249 (accept_3_4 10 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 249 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 249 (accept_3_4 7 71 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 249 (accept_3_4 4 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  249 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 249 (accept_3_4 1 71 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 249
  (allA_succ_of_accept 69 70 249 (Polychromatic418967fa.accept_11_3_4_7_1_114 69 70 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 249 (accept_3_5 68 70 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 70 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 66
  70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 249 (accept_3_5 65 70
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 249 (Polychromatic418967fa.accept_9_1_7_6_1_75
  64 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 249 (accept_3_5 62 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 249 (Polychromatic418967fa.accept_17_9_2_11_1_4042 60 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 249 (accept_3_5 59 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 70 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 249 (accept_3_5 56 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 249 (accept_3_5 53 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 249 (Polychromatic418967fa.accept_11_8_4_7_1_1303 52 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 249 (accept_3_5 50 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 249 (accept_3_5 47 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 249
  (Polychromatic418967fa.accept_16_13_6_9_1_2561 45 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 249 (accept_3_5 44 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 249 (accept_3_5 41 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 249 (accept_3_5 38 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 249 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 249 (accept_3_5 35 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 249 (Polychromatic418967fa.accept_15_4_10_9_1_4298 34 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 249
  (Polychromatic418967fa.accept_13_7_5_2_1_401 33 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 249 (accept_3_5 32 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 249 (accept_3_5 29 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 249 (accept_3_5 26 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 249 (Polychromatic418967fa.accept_18_6_16_15_1_7287 24 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 249 (accept_3_5 23 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 70 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 249 (accept_3_5 20 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 249 (accept_3_5 17 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 249 (Polychromatic418967fa.accept_13_3_5_2_1_1475 16 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 249 (accept_3_5 14 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 249 (accept_3_5 11 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 70 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 249
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 249 (accept_3_5 8 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 70 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 249 (accept_3_5 5 70 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 70 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 249 (accept_3_5 2 70 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 249 (allA_succ_of_accept 68 69
  249 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 249 (Polychromatic418967fa.accept_19_10_12_2_1_6948 67 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 249 3 22 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 65
  69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 249
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 64 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 69 249 3 21 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 69 249 (Polychromatic418967fa.accept_16_14_5_9_1_5901 62 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 69 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 249 3 20 23 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 249 3 19 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 249
  (Polychromatic418967fa.accept_21_14_6_18_1_12047 56 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 69 249 (Polychromatic418967fa.accept_19_17_12_2_1_6880 55 69 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 249 3 18 23 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 249
  (Polychromatic418967fa.accept_21_11_6_18_1_4450 53 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 249 3 17 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 249 (Polychromatic418967fa.accept_13_11_4_2_1_2954
  50 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 249
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 49 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 69 249 3 16 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 69 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 249 (Polychromatic418967fa.accept_16_14_5_9_1_5901 46 69
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 249 3 15 23 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 249 (Polychromatic418967fa.accept_11_10_3_7_1_2564 43 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 249 3 14 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 249 (Polychromatic418967fa.accept_17_7_1_11_1_1894
  41 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 69 249 3 13 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 69 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 69 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 249 3 12 23 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 249
  (Polychromatic418967fa.accept_21_14_6_18_1_12047 35 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 69 249 (Polychromatic418967fa.accept_21_13_6_18_1_10696 34 69 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 249 3 11 23 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 249
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 249 3 10 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 249 (Polychromatic418967fa.accept_16_13_5_9_1_4682
  29 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 28 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 249 3 9 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 249 (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 69
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 249 3 8 23 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 249 (Polychromatic418967fa.accept_19_3_12_2_1_9788 22 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 249 3 7 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 69 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 249 3 6 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 69 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 249 3 5 23 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 249
  (Polychromatic418967fa.accept_16_14_5_9_1_5901 14 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 249 (Polychromatic418967fa.accept_16_13_5_9_1_4682 13 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 249 3 4 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 249 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 69 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 249 3 3 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 249 (Polychromatic418967fa.accept_17_8_1_11_1_4004 8 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 249 (Polychromatic418967fa.accept_17_7_1_11_1_1894 7 69 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 249 3 2 23 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 69 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 249 3 1 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 69 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 249
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 1 69 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 249
  (allA_succ_of_accept 67 68 249 (accept_3_4 67 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  68 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 249 (accept_3_4 64 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 249 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 249 (accept_3_4 61 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 249 (Polychromatic418967fa.accept_16_12_4_9_1_4633 60 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 249 (accept_3_4 58 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 249 (accept_3_4 55 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 249 (accept_3_4 52 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 249 (accept_3_4 49 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 249 (accept_3_4 46 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 249 (accept_3_4 43 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 249 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 249 (accept_3_4 40 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 249 (accept_3_4 37 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 249 (accept_3_4 34 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 249 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 249
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 32 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 249 (accept_3_4 31 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 249 (accept_3_4 28 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 249 (accept_3_4 25 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 249 (accept_3_4 22 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 249 (accept_3_4 19 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 249 (accept_3_4 16 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 249
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 249 (accept_3_4 13 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 249 (accept_3_4 10 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 68 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 249 (accept_3_4 7 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  249 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 249 (accept_3_4 4 68 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 68 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  68 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 249 (accept_3_4 1 68 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 249 (allA_succ_of_accept 66 67
  249 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 249 (accept_3_5 65 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 249 (accept_3_5 62 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 249
  (Polychromatic418967fa.accept_16_12_3_9_1_5886 60 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 249 (accept_3_5 59 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 249 (accept_3_5 56 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 249 (accept_3_5 53 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 249 (accept_3_5 50 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 249 (Polychromatic418967fa.accept_17_15_16_11_1_4001 49 67 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 249 (accept_3_5 47 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 249 (Polychromatic418967fa.accept_20_5_7_9_1_6425 45 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 249 (accept_3_5 44 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 249 (accept_3_5 41 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 249 (accept_3_5 38 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 249
  (Polychromatic418967fa.accept_19_17_10_2_1_9793 36 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 249 (accept_3_5 35 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 249 (Polychromatic418967fa.accept_21_12_4_18_1_4424 33 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 249 (accept_3_5 32 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 249 (Polychromatic418967fa.accept_15_1_7_9_1_20 31 67 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 249 (accept_3_5 29 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 249 (accept_3_5 26 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 249
  (Polychromatic418967fa.accept_19_5_10_2_1_1731 24 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 249 (accept_3_5 23 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 249 (accept_3_5 20 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 249 (accept_3_5 17 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 249 (accept_3_5 14 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 249 (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 249 (accept_3_5 11 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 249 (Polychromatic418967fa.accept_21_9_4_18_1_7615 9 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 249 (accept_3_5 8 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 249 (accept_3_5 5 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 249 (accept_3_5 2 67 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 67 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 249 (allA_succ_of_accept 65 66
  249 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 249 3 21 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 62
  66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 249 3 20 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 249 3 19 22 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 249 3 18 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 249 3 17 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 249 3 16 22 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 249 3 15 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 249 3 14 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 249 3 13 22 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 249 3 12 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 249 3 11 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 249 3 10 22 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 249 3 9 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 249 3 8 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 249 3 7 22 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 249 3 6 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 249 3 5 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 249 3 4 22 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 249 3 3 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 249 3 2 22 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 66 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 249 3 1 22 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 66 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 249 (allA_succ_of_accept 64 65 249 (accept_3_4 64 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 65 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 65 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 249 (accept_3_4 61 65 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 249
  (Polychromatic418967fa.accept_18_6_11_15_1_7255 60 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 65 249 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 65 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 249 (accept_3_4 58 65 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 65 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 56
  65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 249 (accept_3_4 55 65
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 65 249 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 65 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 249 (accept_3_4 52 65 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 65 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 50
  65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 249 (accept_3_4 49 65
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 65 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 249 (accept_3_4 46 65 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 65 249 (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 65 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 249 (accept_3_4 43 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 249 (Polychromatic418967fa.accept_15_12_5_9_1_3234 42 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 249 (accept_3_4 40 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 65 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 249 (accept_3_4 37 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 249 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 249 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 249 (accept_3_4 34 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 65 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 249 (accept_3_4 31 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 249 (Polychromatic418967fa.accept_15_14_5_9_1_2284 29 65 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 249 (accept_3_4 28 65 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 65 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 249 (accept_3_4 25 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 249 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 249 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 249 (accept_3_4 22 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 249 (accept_3_4 19 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 249 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 249 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 249 (accept_3_4 16 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 65 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 249 (accept_3_4 13 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 249 (accept_3_4 10 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 249 (Polychromatic418967fa.accept_18_9_11_15_1_4616 9 65 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 249 (accept_3_4 7 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  249 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 65 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 249 (accept_3_4 4 65 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 65 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 249 (accept_3_4 1 65 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 249 (allA_succ_of_accept 63 64 249
  (Polychromatic418967fa.accept_10_3_4_9_1_15 63 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 249 (accept_3_5 62 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 249 (Polychromatic418967fa.accept_11_5_9_7_1_411 60 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 249 (accept_3_5 59 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 249 (accept_3_5 56 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 249 (accept_3_5 53 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 249
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 51 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 249 (accept_3_5 50 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 249 (accept_3_5 47 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 249 (Polychromatic418967fa.accept_11_2_9_7_1_124 46 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 249 (accept_3_5 44 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 249 (Polychromatic418967fa.accept_12_6_4_9_1_544 42 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 249 (accept_3_5 41 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 249 (accept_3_5 38 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 249 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 249 (accept_3_5 35 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 64 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 249 (accept_3_5 32 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 249 (accept_3_5 29 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 249
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 249 (accept_3_5 26 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 249 (accept_3_5 23 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 249 (accept_3_5 20 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 249 (accept_3_5 17 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 249
  (Polychromatic418967fa.accept_10_5_4_9_1_420 15 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 249 (accept_3_5 14 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 249 (accept_3_5 11 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 64 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 249
  (Polychromatic418967fa.accept_18_9_10_15_1_7254 9 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 249 (accept_3_5 8 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 249 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 64 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 249 (accept_3_5 5 64 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 64 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  64 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 249 (accept_3_5 2 64 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 249 (allA_succ_of_accept 62 63 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 249 3 20 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 249 (Polychromatic418967fa.accept_11_4_8_7_1_819 59
  63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 249 3 19 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 249 (Polychromatic418967fa.accept_10_6_3_9_1_1207 56 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 63 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 249 3 18 21 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 249
  (Polychromatic418967fa.accept_12_5_3_9_1_541 53 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 249 (Polychromatic418967fa.accept_14_10_7_11_1_3015 52 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 249 3 17 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 249 3 16 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 249 3 15 21 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 249
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 249 3 14 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 249
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 40 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 249 3 13 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 249 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 63 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 249 3 12 21 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 249
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 249 3 11 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 249 (Polychromatic418967fa.accept_14_4_7_11_1_790
  32 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 249 3 10 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 249 (Polychromatic418967fa.accept_15_13_3_9_1_1482 28 63
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 249 3 9 21 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 249 3 8 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 249 3 7 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 249 (Polychromatic418967fa.accept_15_5_3_9_1_283 20 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 249 3 6 21 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 249
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 249 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 249 3 5 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 249 3 4 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 249 3 3 21 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 249
  (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 249 3 2 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 63 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 249
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 63 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 249 3 1 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 249 (allA_succ_of_accept 61 62 249
  (accept_3_4 61 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 249
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 249 (accept_3_4 58 62 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 56
  62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 249 (accept_3_4 55 62
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 62 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 249 (accept_3_4 52 62 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 249 (Polychromatic418967fa.accept_9_5_8_6_1_281 50
  62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 249 (accept_3_4 49 62
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 249 (Polychromatic418967fa.accept_9_3_8_6_1_80
  48 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 62 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 62 249 (accept_3_4 46 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  62 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 62 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 249 (accept_3_4 43 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 62 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 62 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 62 249 (accept_3_4 40 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  62 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 62 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 249 (accept_3_4 37 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 249 (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 62 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 249 (accept_3_4 34 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 249 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 249 (accept_3_4 31 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 62 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 249 (accept_3_4 28 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 249 (accept_3_4 25 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 62 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 249 (accept_3_4 22 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 249 (accept_3_4 19 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 62 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 249 (accept_3_4 16 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 249 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 249 (accept_3_4 13 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 62 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 249 (accept_3_4 10 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 249 (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 249 (accept_3_4 7 62 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 62 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 249 (accept_3_4 4 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 62 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 249 (accept_3_4 1 62 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 249
  (allA_succ_of_accept 60 61 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 61 249 (accept_3_5 59 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 61 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 61 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 57
  61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 249 (accept_3_5 56 61
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 61 249 (Polychromatic418967fa.accept_16_6_13_9_1_4690 54 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 61 249 (accept_3_5 53 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 61 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 61 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 51
  61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 249 (accept_3_5 50 61
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 249
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 61 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 61 249 (accept_3_5 47 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 61 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 61 249 (Polychromatic418967fa.accept_10_5_1_9_1_791
  45 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 249 (accept_3_5 44
  61 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 61 249 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 61 249 (accept_3_5 41 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 61 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 39
  61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 249 (accept_3_5 38 61
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 61 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 249 (accept_3_5 35 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 61 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 249 (Polychromatic418967fa.accept_13_7_9_2_1_2167
  33 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 249 (accept_3_5 32
  61 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 249
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 61 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 249 (accept_3_5 29 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 61 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 27
  61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 249 (accept_3_5 26 61
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 249
  (Polychromatic418967fa.accept_10_5_1_9_1_791 25 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 61 249 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 249 (accept_3_5 23 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 61 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 249 (accept_3_5 20 61
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 249 (Polychromatic418967fa.accept_9_1_7_6_1_75
  19 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 249
  (Polychromatic418967fa.accept_10_8_1_9_1_413 18 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 249 (accept_3_5 17 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 249 (accept_3_5 14 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 249 (accept_3_5 11 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 249 (accept_3_5 8 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 249 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 61 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 249 (accept_3_5 5 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 249 (accept_3_5 2 61 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 249 (allA_succ_of_accept 59 60 249 (Polychromatic418967fa.accept_13_7_8_2_1_1483 59 60 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 249
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 58 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 249 3 19 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 249 (Polychromatic418967fa.accept_16_8_12_9_1_2569 56 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 249 (Polychromatic418967fa.accept_19_17_3_2_1_1725 55 60
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 249 3 18 20 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 249
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 249 (Polychromatic418967fa.accept_16_4_12_9_1_2567 52 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 249 3 17 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 249 (Polychromatic418967fa.accept_14_8_4_11_1_3035
  50 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 249
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 249 3 16 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 249 (Polychromatic418967fa.accept_18_11_6_15_1_5953 47 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 249 (Polychromatic418967fa.accept_13_7_8_2_1_1483 46 60 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 249 3 15 20 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 249
  (Polychromatic418967fa.accept_19_6_3_2_1_4119 44 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 249 (Polychromatic418967fa.accept_14_1_4_11_1_3036 43 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 249 3 14 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 249 (Polychromatic418967fa.accept_18_5_6_15_1_3413
  41 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 249
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 40 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 60 249 3 13 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 249 (Polychromatic418967fa.accept_23_15_14_19_1_15033 38 60 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 37
  60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 249 3 12 20 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 249
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 35 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 249 (Polychromatic418967fa.accept_16_2_12_9_1_2568 34 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 249 3 11 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 249 (Polychromatic418967fa.accept_13_6_8_2_1_1484
  32 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 249
  (Polychromatic418967fa.accept_11_9_5_7_1_815 31 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 249 3 10 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 249 (Polychromatic418967fa.accept_18_10_6_15_1_3412 28 60
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 249 3 9 20 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 249
  (Polychromatic418967fa.accept_31_26_29_1_1_15032 26 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 60 249 (Polychromatic418967fa.accept_17_8_9_11_1_3976 25 60 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 249 3 8 20 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 249
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 249 (Polychromatic418967fa.accept_14_8_4_11_1_3035 22 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 249 3 7 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 249 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 60 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 249
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 249 3 6 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 249 (Polychromatic418967fa.accept_18_17_6_15_1_8704 17 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 249 (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 60
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 249 3 5 20 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 249
  (Polychromatic418967fa.accept_22_14_16_7_1_5478 14 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 249 3 4 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 249 (Polychromatic418967fa.accept_18_11_6_15_1_5953 11 60
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 249
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 60 249 3 3 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 60 249 (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 249 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 60 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 249 3 2 20 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 249
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 249 (Polychromatic418967fa.accept_16_4_12_9_1_2567 4 60 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 249 3 1 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 249 (Polychromatic418967fa.accept_16_2_12_9_1_2568 2 60 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 249
  (Polychromatic418967fa.accept_14_1_4_11_1_3036 1 60 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 249 (allA_succ_of_accept 58
  59 249 (accept_3_4 58 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 249 (accept_3_4 55 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 249 (Polychromatic418967fa.accept_9_8_5_6_1_538 53
  59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 249 (accept_3_4 52 59
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 249
  (Polychromatic418967fa.accept_12_3_11_9_1_193 51 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 249 (accept_3_4 49 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 249 (Polychromatic418967fa.accept_9_2_5_6_1_536 47
  59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 249 (accept_3_4 46 59
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 249
  (Polychromatic418967fa.accept_18_9_5_15_1_2246 45 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 59 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 249 (accept_3_4 43 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 41
  59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 249 (accept_3_4 40 59
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 249
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 249 (accept_3_4 37 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 59 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 249 (Polychromatic418967fa.accept_9_8_5_6_1_538 35
  59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 249 (accept_3_4 34 59
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 249
  (Polychromatic418967fa.accept_20_13_19_9_1_10976 33 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 249 (accept_3_4 31 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 249 (accept_3_4 28 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 249 (accept_3_4 25 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 249 (Polychromatic418967fa.accept_18_6_5_15_1_7292 24 59 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 249
  (Polychromatic418967fa.accept_15_8_14_9_1_4216 23 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 249 (accept_3_4 22 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 249 (accept_3_4 19 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 249 (accept_3_4 16 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 249 (accept_3_4 13 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 59 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 249 (accept_3_4 10 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 249 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 249 (accept_3_4 7 59 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 249
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 249 (accept_3_4 4 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  249 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 249 (accept_3_4 1 59 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 249
  (allA_succ_of_accept 57 58 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 58 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 249 (accept_3_5 56 58 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 54
  58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 249 (accept_3_5 53 58
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 249
  (Polychromatic418967fa.accept_9_7_4_6_1_273 52 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 249 (accept_3_5 50 58 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 48
  58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 249 (accept_3_5 47 58
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 249 (Polychromatic418967fa.accept_9_1_4_6_1_5
  46 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 249
  (Polychromatic418967fa.accept_18_9_4_15_1_555 45 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 249 (accept_3_5 44 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 249 (accept_3_5 41 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 58 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 249 (accept_3_5 38 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 249 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 58 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 249 (accept_3_5 35 58 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 58 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 249 (accept_3_5 32 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 249 (accept_3_5 29 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 58 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 249 (accept_3_5 26 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 249 (accept_3_5 23 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 249 (Polychromatic418967fa.accept_13_9_6_2_1_2200 22 58 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 249 (accept_3_5 20 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 249 (accept_3_5 17 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 58 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 249 (accept_3_5 14 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 249 (accept_3_5 11 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 58 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 249
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 249 (accept_3_5 8 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 58 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 249 (accept_3_5 5 58 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 58 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 249 (accept_3_5 2 58 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 249 (allA_succ_of_accept 56 57 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 249 3 18 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 52 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 249 3 17 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 249 3 16 19 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 249 3 15 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 249 3 14 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 57 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 249 3 13 19 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 249 3 12 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 249 3 11 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 57 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 249 3 10 19 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 249 3 9 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 57 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 249 3 8 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 249 3 7 19 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 249 3 6 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 249 3 5 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 249 3 4 19 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 249 3 3 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 249 3 2 19 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 57 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 249 3 1 19 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 57 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 249))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 249 (allA_succ_of_accept 55 56 249 (accept_3_4 55 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 56 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 249 (accept_3_4 52 56 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 249 (Polychromatic418967fa.accept_13_12_4_2_1_2955
  51 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 249 (accept_3_4 49 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 249 (accept_3_4 46 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 56 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 249 (accept_3_4 43 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 249 (accept_3_4 40 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 249
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 38 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 249 (accept_3_4 37 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 249 (Polychromatic418967fa.accept_15_6_11_9_1_3215 36 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 249 (accept_3_4 34 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 249 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 56 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 249 (accept_3_4 31 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 249 (accept_3_4 28 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 249 (Polychromatic418967fa.accept_20_7_16_9_1_4970 27 56 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 249 (accept_3_4 25 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 249 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 249 (accept_3_4 22 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 249
  (Polychromatic418967fa.accept_15_5_11_9_1_4276 20 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 249 (accept_3_4 19 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 249 (accept_3_4 16 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 56 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 249 (accept_3_4 13 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 249 (accept_3_4 10 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 249 (Polychromatic418967fa.accept_19_9_18_2_1_8383 9 56 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 249 (accept_3_4 7 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  249 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 56 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 249 (accept_3_4 4 56 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 249
  (Polychromatic418967fa.accept_15_2_11_9_1_263 2 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 249 (accept_3_4 1 56 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  249)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 249 (allA_succ_of_accept 54 55 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 249 (accept_3_5 53 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 249 (accept_3_5 50 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 55 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 249 (accept_3_5 47 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 249 (accept_3_5 44 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 55 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 249 (accept_3_5 41 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 249 (accept_3_5 38 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 55 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 249
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 249 (accept_3_5 35 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 249 (accept_3_5 32 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 249 (accept_3_5 29 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 249 (accept_3_5 26 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 55 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 249 (accept_3_5 23 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 249 (accept_3_5 20 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 249 (accept_3_5 17 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 249 (accept_3_5 14 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 249 (accept_3_5 11 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 249 (accept_3_5 8 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 249 (accept_3_5 5 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 55 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 249 (accept_3_5 2 55 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 55 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 249)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 249 (allA_succ_of_accept 53 54 249 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 54 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 249
  (Polychromatic418967fa.accept_12_4_6_9_1_548 52 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 54 249 3 17 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 54 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 249 (Polychromatic418967fa.accept_19_11_16_2_1_9759 49 54
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 249 3 16 18 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 249 3 15 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 44
  54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 249 3 14 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 249 3 13 18 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 249
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 249 3 12 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 34 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 54 249 3 11 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 54 249 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 249 3 10 18 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 249 3 9 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 249 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 54 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 249
  (Polychromatic418967fa.accept_10_5_4_9_1_420 25 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 249 3 8 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 54 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 249 3 7 18 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 249 3 6 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 249 (Polychromatic418967fa.accept_19_17_16_2_1_8390 17 54
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 16 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 54 249 3 5 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 54 249 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 249 3 4 18 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 249 3 3 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 54 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 249 3 2 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 249 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 54 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 249 3 1 18 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 54 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 249)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  249 (allA_succ_of_accept 52 53 249 (accept_3_4 52 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 249 (accept_3_4 49 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 53 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 249 (accept_3_4 46 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 249 (Polychromatic418967fa.accept_13_6_1_2_1_1464 45 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 249 (accept_3_4 43 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 249 (Polychromatic418967fa.accept_13_3_1_2_1_2960 42 53 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 249 (accept_3_4 40 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 249 (accept_3_4 37 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 53 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 249
  (Polychromatic418967fa.accept_11_2_9_7_1_124 35 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 249 (accept_3_4 34 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 249 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 249 (accept_3_4 31 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 53 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 249 (accept_3_4 28 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 249 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 249 (accept_3_4 25 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 249 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 53 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 249 (accept_3_4 22 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 249 (accept_3_4 19 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 249 (Polychromatic418967fa.accept_15_3_8_9_1_795 18 53 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 249
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 17 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 249 (accept_3_4 16 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 249 (accept_3_4 13 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 53 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 249 (accept_3_4 10 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 249 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 249 (accept_3_4 7 53 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 249 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 53 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 249 (accept_3_4 4 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  249 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 53 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 249 (accept_3_4 1 53 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 249))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 249
  (allA_succ_of_accept 51 52 249 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 52 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 249 (accept_3_5 50 52 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 48
  52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 249 (accept_3_5 47 52
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 249 (Polychromatic418967fa.accept_9_1_7_6_1_75
  46 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 249
  (Polychromatic418967fa.accept_8_5_4_1_1_111 45 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 52 249 (accept_3_5 44 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  52 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 52 249 (Polychromatic418967fa.accept_12_6_4_9_1_544 42 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 249 (accept_3_5 41 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 52 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 249 (accept_3_5 38 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 249 (accept_3_5 35 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 52 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 249
  (Polychromatic418967fa.accept_23_10_6_19_1_11862 33 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 52 249 (accept_3_5 32 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 52 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 52 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 249 (accept_3_5 29 52 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 28
  52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 249 (accept_3_5 26 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 249 (Polychromatic418967fa.accept_16_8_4_9_1_4666 24 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 249 (accept_3_5 23 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 52 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 249
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 249 (accept_3_5 20 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 249 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 249 (accept_3_5 17 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 249 (Polychromatic418967fa.accept_15_1_7_9_1_20 16 52 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 249 (accept_3_5 14 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 249 (accept_3_5 11 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 52 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 249
  (Polychromatic418967fa.accept_18_9_16_15_1_2241 9 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 249 (accept_3_5 8 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 52 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 249 (accept_3_5 5 52 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 52 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 249 (accept_3_5 2 52 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  249)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 249 (allA_succ_of_accept 50 51 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 249 3 16 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 47
  51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 249 3 15 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 249 (Polychromatic418967fa.accept_13_5_12_2_1_1423 44 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 51 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 249 3 14 17 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 249 3 13 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 249 3 12 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 249 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 249 3 11 17 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 249
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 249 3 10 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 29
  51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 249
  (Polychromatic418967fa.accept_10_8_1_9_1_413 28 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 249 3 9 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 249 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 51 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 249 3 8 17 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 249
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 249 3 7 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 51 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 249 3 6 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 249 (Polychromatic418967fa.accept_13_3_12_2_1_385 16 51 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 249 3 5 17 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 249 3 4 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 51 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 249 3 3 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 249 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 249 3 2 17 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 249 (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 51 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 249 3 1 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 51 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 249))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 249 (allA_succ_of_accept 49 50 249
  (accept_3_4 49 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 249
  (Polychromatic418967fa.accept_9_3_5_6_1_253 48 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 249 (accept_3_4 46 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 50 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 249 (Polychromatic418967fa.accept_9_8_5_6_1_538 44
  50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 249 (accept_3_4 43 50
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 249
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 249 (accept_3_4 40 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 38
  50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 249 (accept_3_4 37 50
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 249
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 249 (accept_3_4 34 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 50 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 249 (Polychromatic418967fa.accept_14_4_8_11_1_794
  32 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 249 (accept_3_4 31
  50 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 249
  (Polychromatic418967fa.accept_9_3_5_6_1_253 30 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 50 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 249 (accept_3_4 28 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 50 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 26
  50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 50 249 (accept_3_4 25 50
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 50 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 249 (accept_3_4 22 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 50 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 50 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 249 (Polychromatic418967fa.accept_9_2_5_6_1_536 20
  50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 50 249 (accept_3_4 19 50
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 249
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 249 (accept_3_4 16 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 50 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 249 (Polychromatic418967fa.accept_15_14_5_9_1_2284
  14 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 249 (accept_3_4 13
  50 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 50 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 249 (accept_3_4 10 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 50 249 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 50 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 249 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 249 (accept_3_4 7 50 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 6
  50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 50 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 50 249 (accept_3_4 4 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 249 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 249 (accept_3_4 1 50 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 249)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 249 (allA_succ_of_accept
  48 49 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 49 249 (accept_3_5 47 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 49 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 249 (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 49
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 249 (accept_3_5 44 49 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 43
  49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 249
  (Polychromatic418967fa.accept_11_9_5_7_1_815 42 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 249 (accept_3_5 41 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 249 (accept_3_5 38 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 249
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 249 (accept_3_5 35 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 249 (Polychromatic418967fa.accept_17_16_15_11_1_10421 33 49 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 249 (accept_3_5 32 49 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 249 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 49 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 249 (accept_3_5 29 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 249 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 249 (accept_3_5 26 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 249
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 249 (accept_3_5 23 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 249 (accept_3_5 20 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 249
  (Polychromatic418967fa.accept_13_5_10_2_1_856 18 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 249 (accept_3_5 17 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 249 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 249 (accept_3_5 14 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 249 (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 49 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 249 (accept_3_5 11 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 249 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 249 (accept_3_5 8 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 49 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 249
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 6 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 249 (accept_3_5 5 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 49 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 249 (accept_3_5 2 49 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 249))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 249 (allA_succ_of_accept 47 48 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 249 3 15 16 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 249 3 14 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 249 3 13 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 249 3 12 16 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 249 3 11 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 249 3 10 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 48 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 249 3 9 16 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 249 3 8 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 249 3 7 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 249 3 6 16 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 249 3 5 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 48 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 249 3 4 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 48 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 249 3 3 16 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 249 3 2 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 48 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 249 3 1 16 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 48 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  249)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 249 (allA_succ_of_accept 46 47 249 (accept_3_4 46 47
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 249
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 249 (accept_3_4 43 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 249 (accept_3_4 40 47
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 249
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 249 (accept_3_4 37 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 249 (Polychromatic418967fa.accept_9_8_2_6_1_875 35
  47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 249 (accept_3_4 34 47
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 249
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 249 (accept_3_4 31 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 249 (accept_3_4 28 47
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 249 (accept_3_4 25 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 249 (Polychromatic418967fa.accept_16_8_15_9_1_4676 24 47 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 249 (accept_3_4 22 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 249 (accept_3_4 19 47 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 249 (accept_3_4 16 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 249 (accept_3_4 13 47 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 249
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 249 (accept_3_4 10 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 249 (accept_3_4 7 47 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 249 (accept_3_4 4 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  249 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 249 (accept_3_4 1 47 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 249))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 249 (allA_succ_of_accept 45
  46 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 46 249 (accept_3_5 44 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 46 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 249 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 46 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 249 (accept_3_5 41 46 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 40
  46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 249 (accept_3_5 38 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 249 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 46 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 249 (accept_3_5 35 46 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 46 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 249
  (Polychromatic418967fa.accept_10_3_6_9_1_779 33 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 249 (accept_3_5 32 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 46 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 249 (accept_3_5 29 46 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 249 (Polychromatic418967fa.accept_21_7_4_18_1_4471 28 46 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 249 (accept_3_5 26 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 249 (Polychromatic418967fa.accept_18_6_10_15_1_9963 24 46 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 249 (accept_3_5 23 46 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 46 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 249 (accept_3_5 20 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 46 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 249 (accept_3_5 17 46 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 46 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 249 (accept_3_5 14 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 46 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 249 (accept_3_5 11 46 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 249 (Polychromatic418967fa.accept_15_10_1_9_1_5356 10 46 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 249
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 249 (accept_3_5 8 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 46 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 249 (accept_3_5 5 46 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 46 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 249 (accept_3_5 2 46 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  249)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 249 (allA_succ_of_accept 44 45 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 249 3 14 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 41
  45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 249
  (Polychromatic418967fa.accept_13_1_6_2_1_377 40 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 249 3 13 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 249 (Polychromatic418967fa.accept_13_12_6_2_1_1441 38 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 249 (Polychromatic418967fa.accept_16_5_13_9_1_2594 37 45
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 249 3 12 15 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 249
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 249 3 11 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 249 (Polychromatic418967fa.accept_19_13_7_2_1_5413
  32 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 249
  (Polychromatic418967fa.accept_10_1_5_9_1_157 31 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 249 3 10 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 45 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 249 3 9 15 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 249
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 26 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 249 (Polychromatic418967fa.accept_13_12_6_2_1_1441 25 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 249 3 8 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 249 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 45 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 249 3 7 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 249 (Polychromatic418967fa.accept_21_19_3_18_1_7510 19 45
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 249 3 6 15 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 249
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 249 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 249 3 5 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 249 (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 45 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 249 3 4 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 249 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 45
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 249 3 3 15 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 249 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 249 3 2 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 249 (Polychromatic418967fa.accept_16_5_13_9_1_2594 5 45 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 45 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 249 3 1 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 249 (Polychromatic418967fa.accept_21_2_3_18_1_5952 2 45 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 45 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  249))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 249 (allA_succ_of_accept 43 44 249 (accept_3_4 43 44
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 249
  (Polychromatic418967fa.accept_12_6_8_9_1_553 42 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 249 (accept_3_4 40 44 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 249 (accept_3_4 37 44
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 249
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 249 (accept_3_4 34 44 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 249 (Polychromatic418967fa.accept_9_5_8_6_1_281 32
  44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 249 (accept_3_4 31 44
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 249 (Polychromatic418967fa.accept_9_3_8_6_1_80
  30 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 249 (accept_3_4 28 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 249 (accept_3_4 25 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 249 (Polychromatic418967fa.accept_16_8_12_9_1_2569 24 44 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 249 (accept_3_4 22 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 249 (accept_3_4 19 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 44 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 249 (accept_3_4 16 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 249 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 249 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 249 (accept_3_4 13 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 44 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 249 (accept_3_4 10 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 249 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 249 (accept_3_4 7 44 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 44 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 249 (accept_3_4 4 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  249 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 44 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 44 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 249 (accept_3_4 1 44 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 249)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 249 (allA_succ_of_accept 42 43
  249 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 249 (accept_3_5 41 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 249 (accept_3_5 38 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 43 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 249
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 249 (accept_3_5 35 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 249 (accept_3_5 32 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 249 (accept_3_5 29 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 249 (accept_3_5 26 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 249 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 43 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 249 (accept_3_5 23 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 249 (accept_3_5 20 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 249 (accept_3_5 17 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 249 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 249 (accept_3_5 14 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 43 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 249 (accept_3_5 11 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 249 (Polychromatic418967fa.accept_21_9_1_18_1_1761 9 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 249 (accept_3_5 8 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 249 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 43 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 249 (accept_3_5 5 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 43 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 249 (accept_3_5 2 43 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 249))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 249
  (allA_succ_of_accept 41 42 249 (Polychromatic418967fa.accept_10_1_2_9_1_152 41 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 42 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 249 3 13 14 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 249
  (Polychromatic418967fa.accept_11_5_9_7_1_411 38 42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 249 (Polychromatic418967fa.accept_10_7_2_9_1_775 37 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 249 3 12 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 249
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 249 3 11 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 249 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 249 3 10 14 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 249
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 29 42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 249 3 9 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 249 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 42 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 249
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 249 3 8 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 42 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 249 3 7 14 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 249
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 249 3 6 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 249 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 42 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 249
  (Polychromatic418967fa.accept_11_5_9_7_1_411 16 42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 249 3 5 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 249 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 249 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 42 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 249 3 4 14 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 249 3 3 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 249 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 42 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 249 3 2 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 249 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 42 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 249 3 1 14 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 249
  (Polychromatic418967fa.accept_11_2_9_7_1_124 2 42 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 249 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 42 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 249)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 249
  (allA_succ_of_accept 40 41 249 (accept_3_4 40 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 249 (accept_3_4 37 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 249 (Polychromatic418967fa.accept_15_6_11_9_1_3215 36 41 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 249 (accept_3_4 34 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 249 (accept_3_4 31 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 41 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 249 (accept_3_4 28 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 249 (accept_3_4 25 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 249 (accept_3_4 22 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 249 (accept_3_4 19 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 249 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 41 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 249 (accept_3_4 16 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 249 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 249 (accept_3_4 13 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 249 (accept_3_4 10 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 249 (accept_3_4 7 41 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 249 (Polychromatic418967fa.accept_15_6_11_9_1_3215 6 41 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 249 (accept_3_4 4 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  249 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 249 (accept_3_4 1 41 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 249))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 249 (allA_succ_of_accept 39 40 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 249 (accept_3_5 38 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 40 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 249 (accept_3_5 35 40 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 40 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 249
  (Polychromatic418967fa.accept_15_3_10_9_1_769 33 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 249 (accept_3_5 32 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 40 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 249 (accept_3_5 29 40 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 40 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 249 (accept_3_5 26 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 249 (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 40 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 249 (accept_3_5 23 40 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 40 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 249 (accept_3_5 20 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 249 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 40 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 249 (accept_3_5 17 40 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 40 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 249 (accept_3_5 14 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 40 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 249 (accept_3_5 11 40 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 40 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 249 (accept_3_5 8 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 40 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 249 (accept_3_5 5 40 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 249 (Polychromatic418967fa.accept_15_4_10_9_1_4298 4 40 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  40 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 249 (accept_3_5 2 40 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  249)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 249 (allA_succ_of_accept 38 39 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 39 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 249 3 12 13 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 249 3 11 13 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 249 3 10 13 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 249 3 9 13 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 249 3 8 13 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 249 3 7 13 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 249 3 6 13 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 39 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 249 3 5 13 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 39 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 249 3 4 13 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 249 3 3 13 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 39 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 249 3 2 13 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 39 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 249 3 1 13 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 39 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 249))))))))))))))))))))))))))))))))))))))) (allB_succ 38 249
  (allA_succ_of_accept 37 38 249 (accept_3_4 37 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 249 (accept_3_4 34 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 249 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 38 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 249 (accept_3_4 31 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 249 (accept_3_4 28 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 249 (accept_3_4 25 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 249 (accept_3_4 22 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 249 (accept_3_4 19 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 249 (accept_3_4 16 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 249 (accept_3_4 13 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 249 (accept_3_4 10 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 249 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 38 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 249 (accept_3_4 7 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  249 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 249 (accept_3_4 4 38 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 249 (Polychromatic418967fa.accept_15_2_8_9_1_4294 2
  38 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 249 (accept_3_4 1 38 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 249)))))))))))))))))))))))))))))))))))))) (allB_succ 37 249
  (allA_succ_of_accept 36 37 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 249 (accept_3_5 35 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 249 (accept_3_5 32 37
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 249
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 249 (accept_3_5 29 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 249 (accept_3_5 26 37
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 249
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 249 (Polychromatic418967fa.accept_19_5_18_2_1_5404 24 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 249 (accept_3_5 23 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 249 (accept_3_5 20 37
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 249 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 249 (accept_3_5 17 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 249 (Polychromatic418967fa.accept_12_3_1_9_1_202
  15 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 249 (accept_3_5 14
  37 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 249 (accept_3_5 11 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 249 (Polychromatic418967fa.accept_13_9_11_2_1_1491
  9 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 249 (accept_3_5 8 37
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 249 (Polychromatic418967fa.accept_9_7_1_6_1_261
  7 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 249 (accept_3_5 5 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 249 (accept_3_5 2 37 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 249 (Polychromatic418967fa.accept_15_1_7_9_1_20 1 37 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 249))))))))))))))))))))))))))))))))))))) (allB_succ 36 249
  (allA_succ_of_accept 35 36 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 36 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 249 (Polychromatic418967fa.accept_13_8_10_2_1_1450 34 36
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 249 3 11 12 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 249
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 36 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 249 3 10 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 29
  36 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 249
  (Polychromatic418967fa.accept_16_12_4_9_1_4633 28 36 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 249 3 9 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 36 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 249 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 36 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 249 3 8 12 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 249
  (Polychromatic418967fa.accept_10_3_6_9_1_779 23 36 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 249 (Polychromatic418967fa.accept_19_3_17_2_1_6963 22 36 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 249 3 7 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 249 (Polychromatic418967fa.accept_17_3_2_11_1_1895 20 36 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 249 3 6 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 249 (Polychromatic418967fa.accept_13_3_10_2_1_381 16 36 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 249 3 5 12 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 249
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 36 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 36 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 249 3 4 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 249 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 36
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 10 36 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 249 3 3 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 249 (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 36 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 249 (Polychromatic418967fa.accept_19_7_17_2_1_6855 7 36 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 249 3 2 12 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 249 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 36 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 249 3 1 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 249 (Polychromatic418967fa.accept_21_2_15_18_1_806 2 36 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 249
  (Polychromatic418967fa.accept_15_1_6_9_1_254 1 36 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 249)))))))))))))))))))))))))))))))))))) (allB_succ 35 249 (allA_succ_of_accept 34 35 249 (accept_3_4 34
  35 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 249
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 33 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 249 (accept_3_4 31 35 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 29
  35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 249 (accept_3_4 28 35
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 249
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 249 (accept_3_4 25 35 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 249 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 35 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 249 (Polychromatic418967fa.accept_9_5_8_6_1_281 23
  35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 249 (accept_3_4 22 35
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 249 (Polychromatic418967fa.accept_9_3_8_6_1_80
  21 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 249 (accept_3_4 19 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 249 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 35 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 249 (accept_3_4 16 35 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 249 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 35 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 249 (accept_3_4 13 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 249 (accept_3_4 10 35 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 249 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 35 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 249 (accept_3_4 7 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 249 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 35 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 249 (accept_3_4 4 35 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 249 (accept_3_4 1 35 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 249))))))))))))))))))))))))))))))))))) (allB_succ 34 249
  (allA_succ_of_accept 33 34 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 34 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 249 (accept_3_5 32 34 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 34 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 30
  34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 249 (accept_3_5 29 34
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 249 (Polychromatic418967fa.accept_9_1_7_6_1_75
  28 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 249 (accept_3_5 26 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 34 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 249 (accept_3_5 23 34 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 34 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 249 (accept_3_5 20 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 34 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 249 (accept_3_5 17 34 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 34 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 249 (accept_3_5 14 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 34 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 249 (accept_3_5 11 34 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 34 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 249 (accept_3_5 8 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 249 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 34 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 249 (accept_3_5 5 34 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 34 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 249 (accept_3_5 2 34 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 249))))))))))))))))))))))))))))))))))
  (allB_succ 33 249 (allA_succ_of_accept 32 33 249 (Polychromatic418967fa.accept_17_15_16_11_1_4001 32 33 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 249
  (Polychromatic418967fa.accept_13_5_7_2_1_852 31 33 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 249 3 10 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 249 (Polychromatic418967fa.accept_15_13_3_9_1_1482 28 33
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 249 3 9 11 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 249
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 33 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 249 (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 33 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 249 3 8 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 33 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 22 33 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 249 3 7 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 33 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 249 (Polychromatic418967fa.accept_20_19_13_9_1_5019 19 33
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 249 3 6 11 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 249
  (Polychromatic418967fa.accept_19_17_14_2_1_4116 17 33 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 249 3 5 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 249 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 33 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 33 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 249 3 4 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 249 (Polychromatic418967fa.accept_21_11_12_18_1_4455 11 33 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 249 (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 33
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 249 3 3 11 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 33 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 249 (Polychromatic418967fa.accept_19_7_14_2_1_4095 7 33 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 249 3 2 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 249 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 33 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 249
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 33 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 249 3 1 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 33 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 33 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 249)))))))))))))))))))))))))))))))))
  (allB_succ 32 249 (allA_succ_of_accept 31 32 249 (accept_3_4 31 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 32 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 249 (accept_3_4 28 32 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 249 (Polychromatic418967fa.accept_10_7_2_9_1_775
  27 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 249 (accept_3_4 25 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 249 (Polychromatic418967fa.accept_21_3_11_18_1_805 24 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 249 (accept_3_4 22 32 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 249 (accept_3_4 19 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 249 (accept_3_4 16 32 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 249 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 32 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 249
  (Polychromatic418967fa.accept_11_3_10_7_1_129 14 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 249 (accept_3_4 13 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 249 (accept_3_4 10 32 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 249 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 32 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 249 (accept_3_4 7 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  249 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 249 (accept_3_4 4 32 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 249 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  32 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 249 (accept_3_4 1 32 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 249)))))))))))))))))))))))))))))))) (allB_succ 31 249
  (allA_succ_of_accept 30 31 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 249 (accept_3_5 29 31 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 27
  31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 249 (accept_3_5 26 31
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 249
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 249 (Polychromatic418967fa.accept_11_2_9_7_1_124 24 31 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 249 (accept_3_5 23 31 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 249 (accept_3_5 20 31
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 249 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 249 (accept_3_5 17 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 31 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 249 (accept_3_5 14 31 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 31 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 249 (accept_3_5 11 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 249 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 31 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 249 (accept_3_5 8 31 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 249 (accept_3_5 5 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 249 (accept_3_5 2 31 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 249))))))))))))))))))))))))))))))) (allB_succ 30 249
  (allA_succ_of_accept 29 30 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 30 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 30 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 249 3 9 10 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 30 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 30 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 249 3 8 10 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 30 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 249 3 7 10 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 30 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 249 3 6 10 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 30 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 30 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 249 3 5 10 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 30 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 30 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 249 3 4 10 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 30 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 249 3 3 10 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 30 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 249 3 2 10 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 30 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 30 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 249 3 1 10 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 30 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 30 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 249)))))))))))))))))))))))))))))) (allB_succ
  29 249 (allA_succ_of_accept 28 29 249 (accept_3_4 28 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 29 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 249 (accept_3_4 25 29 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 24
  29 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 249 (accept_3_4 22 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 249 (accept_3_4 19 29 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 249 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 29 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 249 (accept_3_4 16 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 249 (accept_3_4 13 29 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 249
  (Polychromatic418967fa.accept_13_11_3_2_1_863 11 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 249 (accept_3_4 10 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 249 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 249 (accept_3_4 7 29 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 249 (Polychromatic418967fa.accept_15_6_14_9_1_1471 6 29 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 249 (accept_3_4 4 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  249 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 29 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 249 (accept_3_4 1 29 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 249))))))))))))))))))))))))))))) (allB_succ 28 249 (allA_succ_of_accept 27 28 249
  (Polychromatic418967fa.accept_10_7_8_9_1_785 27 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 249 (accept_3_5 26 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 28 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 249 (accept_3_5 23 28 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 28 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 249
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 249 (accept_3_5 20 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 249 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 249 (accept_3_5 17 28 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 28 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 249
  (Polychromatic418967fa.accept_19_15_9_2_1_8347 15 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 249 (accept_3_5 14 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 28 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 249 (accept_3_5 11 28 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 249 (Polychromatic418967fa.accept_21_10_7_18_1_12065 10 28 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 249
  (Polychromatic418967fa.accept_18_9_10_15_1_7254 9 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 249 (accept_3_5 8 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 249 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 28 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 249 (accept_3_5 5 28 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 28 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 249 (accept_3_5 2 28 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 249))))))))))))))))))))))))))))
  (allB_succ 27 249 (allA_succ_of_accept 26 27 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 27 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 249 3 8 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 249 3 7 9 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 249
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 27 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 27 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 249 3 6 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 249 3 5 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 27 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 249 3 4 9 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 249
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 27 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 249 3 3 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 249 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 27 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 249 3 2 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 249 (Polychromatic418967fa.accept_15_4_12_9_1_773 4 27 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 249 3 1 9 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 27 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 249))))))))))))))))))))))))))) (allB_succ 26 249 (allA_succ_of_accept 25
  26 249 (accept_3_4 25 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 249
  (Polychromatic418967fa.accept_19_5_7_2_1_1728 24 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 249 (accept_3_4 22 26 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  26 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 249 (accept_3_4 19 26
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 249
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 249 (accept_3_4 16 26 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 249 (Polychromatic418967fa.accept_9_5_8_6_1_281 14
  26 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 249 (accept_3_4 13 26
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 249 (Polychromatic418967fa.accept_9_3_8_6_1_80
  12 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 249 (accept_3_4 10 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 26 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 26 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 249 (accept_3_4 7 26 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 26 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 249 (accept_3_4 4 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 26 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 249 (accept_3_4 1 26 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 249)))))))))))))))))))))))))) (allB_succ 25 249 (allA_succ_of_accept 24 25 249
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 249 (accept_3_5 23 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 249 (accept_3_5 20 25 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 25 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 249
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 249 (accept_3_5 17 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 249 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 25 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 249 (accept_3_5 14 25 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 25 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 249 (accept_3_5 11 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 249 (Polychromatic418967fa.accept_17_9_8_11_1_1040 9 25 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 249 (accept_3_5 8 25 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 249 (Polychromatic418967fa.accept_20_7_5_9_1_10833 7 25 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 249
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 249 (accept_3_5 5 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 25 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 249 (accept_3_5 2 25 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 25 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 249))))))))))))))))))))))))) (allB_succ 24 249
  (allA_succ_of_accept 23 24 249 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 24 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 24 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 249 3 7 8 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 24 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 249 (Polychromatic418967fa.accept_20_19_4_9_1_5025 19 24 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 249 3 6 8 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 249 (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 24 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 249
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 24 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 249 3 5 8 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 249 (Polychromatic418967fa.accept_19_14_5_2_1_6941 14 24 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 249 3 4 8 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 249
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 11 24 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 249 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 24 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 249 3 3 8 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 24 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 249
  (Polychromatic418967fa.accept_14_7_10_11_1_8112 7 24 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 249 3 2 8 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 249 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 24 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 249 (Polychromatic418967fa.accept_13_4_11_2_1_1458 4 24 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 249 3 1 8 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 249
  (Polychromatic418967fa.accept_20_2_4_9_1_9524 2 24 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 249)))))))))))))))))))))))) (allB_succ 23 249 (allA_succ_of_accept 22 23
  249 (accept_3_4 22 23 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 249
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 249 (accept_3_4 19 23 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 249 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  23 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 249 (accept_3_4 16 23
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 249
  (Polychromatic418967fa.accept_12_3_11_9_1_193 15 23 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 249 (accept_3_4 13 23 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 249 (Polychromatic418967fa.accept_9_2_5_6_1_536 11
  23 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 249 (accept_3_4 10 23
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 249
  (Polychromatic418967fa.accept_18_9_5_15_1_2246 9 23 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 249 (accept_3_4 7 23 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 5
  23 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 249 (accept_3_4 4 23 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  23 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 249 (accept_3_4 1 23 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  249))))))))))))))))))))))) (allB_succ 22 249 (allA_succ_of_accept 21 22 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 249 (accept_3_5 20 22 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 22 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 249 (accept_3_5 17 22 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 22 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 249 (accept_3_5 14 22 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 22 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 249 (accept_3_5 11 22 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 22 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 249
  (Polychromatic418967fa.accept_18_9_4_15_1_555 9 22 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 249 (accept_3_5 8 22 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 249 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 22 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 249 (accept_3_5 5 22 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 249 (Polychromatic418967fa.accept_14_4_8_11_1_794 4 22 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 249 (accept_3_5 2 22 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 249)))))))))))))))))))))) (allB_succ 21
  249 (allA_succ_of_accept 20 21 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 21 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 249 3 6 7 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 249 3 5 7 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 249 3 4 7 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 249 3 3 7 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 21 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 249 3 2 7 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 21 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 249 3 1 7 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 249))))))))))))))))))))) (allB_succ 20 249
  (allA_succ_of_accept 19 20 249 (accept_3_4 19 20 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 20 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 249 (accept_3_4 16 20 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 249 (Polychromatic418967fa.accept_19_15_1_2_1_6894 15 20 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 20 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 249 (accept_3_4 13 20 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 20 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 249 (accept_3_4 10 20 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 20 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 20 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 249 (accept_3_4 7 20 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  249 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 20 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 249 (accept_3_4 4 20 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 20 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 20
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 249 (accept_3_4 1 20 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 249)))))))))))))))))))) (allB_succ 19 249 (allA_succ_of_accept
  18 19 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 249 (accept_3_5 17 19 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 19 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 249 (accept_3_5 14 19 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  19 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 249 (accept_3_5 11 19 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 19 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 249 (accept_3_5 8 19 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 249 (accept_3_5 5 19 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 249 (accept_3_5 2 19 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 249))))))))))))))))))) (allB_succ 18 249 (allA_succ_of_accept 17
  18 249 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 18 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 18 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 249 3 5 6 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 249 (Polychromatic418967fa.accept_10_4_8_9_1_784 14
  18 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 249
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 18 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 249 3 4 6 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 249 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 18 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 249 3 3 6 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 249
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 18 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 249 3 2 6 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 249 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 18 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 249
  (Polychromatic418967fa.accept_10_4_8_9_1_784 4 18 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 249 3 1 6 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 249 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 18 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 249 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 18 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 249)))))))))))))))))) (allB_succ 17 249
  (allA_succ_of_accept 16 17 249 (accept_3_4 16 17 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 249 (accept_3_4 13 17 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 17 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 249 (accept_3_4 10 17 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 249 (Polychromatic418967fa.accept_18_9_17_15_1_2267 9 17 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 249 (accept_3_4 7 17 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 17 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 249 (accept_3_4 4 17 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  249 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 249 (accept_3_4 1 17 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 249))))))))))))))))) (allB_succ 16 249 (allA_succ_of_accept 15 16 249
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 16 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 249 (accept_3_5 14 16 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 16 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 249 (accept_3_5 11 16 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 16 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 249
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 16 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 249 (accept_3_5 8 16 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 16 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 249 (accept_3_5 5 16 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 16 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 16
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 249 (accept_3_5 2 16 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 249)))))))))))))))) (allB_succ 15 249
  (allA_succ_of_accept 14 15 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 15 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 249 3 4 5 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 249
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 15 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 249 3 3 5 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 249 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 15 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 15 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 249 3 2 5 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 15 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 249 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 15 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 249 3 1 5 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 15 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 249))))))))))))))) (allB_succ 14 249 (allA_succ_of_accept 13 14 249
  (accept_3_4 13 14 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 249
  (Polychromatic418967fa.accept_9_3_5_6_1_253 12 14 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 249 (accept_3_4 10 14 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 249 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 14 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 249 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  14 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 249 (accept_3_4 7 14 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 6
  14 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 249 (accept_3_4 4 14 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 249 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 14 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 249 (accept_3_4 1 14 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 249)))))))))))))) (allB_succ 13 249 (allA_succ_of_accept 12 13 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 249 (accept_3_5 11 13 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 13 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 249 (accept_3_5 8 13 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 249
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 13 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 249 (accept_3_5 5 13 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 13 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 249 (accept_3_5 2 13 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 249))))))))))))) (allB_succ 12 249 (allA_succ_of_accept 11 12
  249 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 12 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 12 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 249 3 3 4 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 12 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 249
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 249 3 2 4 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 12 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 249 3 1 4 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 12 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 249)))))))))))) (allB_succ 11 249 (allA_succ_of_accept 10 11 249
  (accept_3_4 10 11 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 249
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 11 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 249 (accept_3_4 7 11 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 249 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  11 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 249 (accept_3_4 4 11 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  11 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 249 (accept_3_4 1 11 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  249))))))))))) (allB_succ 10 249 (allA_succ_of_accept 9 10 249 (Polychromatic418967fa.accept_18_9_10_15_1_7254 9 10
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 249 (accept_3_5 8 10 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 10 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 249 (accept_3_5 5 10 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  249 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 10 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 249 (accept_3_5 2 10 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 249)))))))))) (allB_succ 9 249 (allA_succ_of_accept 8 9 249
  (Polychromatic418967fa.accept_17_8_9_11_1_3976 8 9 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 249 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 9 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 249 3 2 3 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 249
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 9 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 249 3 1 3 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 249 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 9 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 249 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 9 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 249))))))))) (allB_succ 8 249
  (allA_succ_of_accept 7 8 249 (accept_3_4 7 8 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 249
  (Polychromatic418967fa.accept_12_6_8_9_1_553 6 8 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 249 (accept_3_4 4 8 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 8 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 8
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 249 (accept_3_4 1 8 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 249)))))))) (allB_succ 7 249 (allA_succ_of_accept 6 7 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 249 (accept_3_5 5 7 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 249
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 249 (accept_3_5 2 7 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 249))))))) (allB_succ 6 249 (allA_succ_of_accept 5 6 249
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 6 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 6 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 249 3 1 2 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 249
  (Polychromatic418967fa.accept_11_1_6_7_1_116 1 6 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 249)))))) (allB_succ 5 249 (allA_succ_of_accept 4 5 249 (accept_3_4 4 5 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 5 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 249 (accept_3_4 1 5 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 249))))) (allB_succ 4 249 (allA_succ_of_accept 3 4 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 4 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 249 (accept_3_5 2 4 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 249
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 249)))) (allB_succ 3 249 (allA_succ_of_accept 2 3 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 3 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 249))) (allB_succ 2 249 (allA_succ_of_accept 1 2 249 (accept_3_4 1 2 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 249)) (allB_two
  249))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


