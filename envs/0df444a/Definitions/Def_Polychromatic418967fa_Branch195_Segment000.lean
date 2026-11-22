-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch195_Segment000
-- name    : Polychromatic418967fa_Branch195_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:29:54.711361+00:00
-- url     : https://prove2.me/theorems/f90a76e3-f3cb-461b-a445-d8613cd8416c
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

def Polychromatic418967fa.branch_195_segment_000 : allB 100 195 :=
  allB_succ' 97 99 195 (Eq.refl Bool.true) (allA_succ_of_gcd 96 99 195 3 32 33 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 99 195
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 95 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 99 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 94 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 195 3 31 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 195 (Polychromatic418967fa.accept_17_7_14_8_1_5069
  92 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 99 195
  (Polychromatic418967fa.accept_10_1_9_5_1_83 91 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 99 195 3 30 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 99 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 195 (Polychromatic418967fa.accept_18_16_9_15_1_4614 88 99
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 99 195 3 29 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 99 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 195 (Polychromatic418967fa.accept_19_9_4_5_1_3019 85 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 195 3 28 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 195 (Polychromatic418967fa.accept_18_11_9_15_1_5988
  83 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 82 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 99 195 3 27 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 99 195 (Polychromatic418967fa.accept_21_17_15_6_1_3557 80 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 99 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 99 195 3 26 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 99 195
  (Polychromatic418967fa.accept_14_7_1_13_1_357 77 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 99 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 76 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 195 3 25 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 74
  99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 195
  (Polychromatic418967fa.accept_21_10_15_6_1_5090 73 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 99 195 3 24 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 99 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 71 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 195 (Polychromatic418967fa.accept_18_16_9_15_1_4614 70 99
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 99 195 3 23 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 99 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 195 (Polychromatic418967fa.accept_17_16_14_8_1_7608 67 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 195 3 22 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 65
  99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 195
  (Polychromatic418967fa.accept_10_4_9_5_1_84 64 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 99 195 3 21 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 99 195 (Polychromatic418967fa.accept_17_11_14_8_1_2729 62 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 99 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 99 195 3 20 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 99 195
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 59 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 99 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 195 3 19 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046
  56 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 195
  (Polychromatic418967fa.accept_21_13_15_6_1_3556 55 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 99 195 3 18 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 99 195 (Polychromatic418967fa.accept_18_17_9_15_1_7268 53 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 195 (Polychromatic418967fa.accept_18_16_9_15_1_4614 52 99
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 99 195 3 17 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 99 195
  (Polychromatic418967fa.accept_17_16_14_8_1_7608 50 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 195 (Polychromatic418967fa.accept_14_7_1_13_1_357 49 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 195 3 16 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 47
  99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 195
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 46 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 99 195 3 15 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 99 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 195 (Polychromatic418967fa.accept_21_1_15_6_1_6620 43 99
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 99 195 3 14 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 99 195
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 195 3 13 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 195 (Polychromatic418967fa.accept_21_17_15_6_1_3557
  38 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 99 195 3 12 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 99 195 (Polychromatic418967fa.accept_14_7_1_13_1_357 35 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 34 99 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 195 3 11 33 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 195
  (Polychromatic418967fa.accept_21_11_15_6_1_3667 32 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 195 3 10 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 195 (Polychromatic418967fa.accept_18_11_9_15_1_5988
  29 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 195
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 28 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 99 195 3 9 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 99 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 195 (Polychromatic418967fa.accept_19_6_4_5_1_5650 25 99 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 195 3 8 33 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 195 (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 195 3 7 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 195 (Polychromatic418967fa.accept_19_1_4_5_1_4313 20 99 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 99 195 3 6 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 99 195 (Polychromatic418967fa.accept_18_17_9_15_1_7268 17 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 99 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 195 3 5 33 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 195
  (Polychromatic418967fa.accept_10_4_9_5_1_84 14 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 195 (Polychromatic418967fa.accept_21_13_15_6_1_3556 13 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 195 3 4 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 99 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 195
  (Polychromatic418967fa.accept_18_10_9_15_1_7267 10 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 99 195 3 3 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 99 195 (Polychromatic418967fa.accept_19_8_4_5_1_8569 8 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 195 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 99 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 195 3 2 33 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 99 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 195 3 1 33 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 99 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 195
  (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 98 195 (allA_succ_of_accept 97 98 195 (accept_3_4 97 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 98 195 (Polychromatic418967fa.accept_19_1_3_5_1_3092 96 98 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 98 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 95 98 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 195 (accept_3_4 94 98 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 93
  98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 92 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 195 (accept_3_4 91 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 195 (accept_3_4 88 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 87 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 86 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 195 (accept_3_4 85 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 84 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 195 (accept_3_4 82 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 195
  (Polychromatic418967fa.accept_24_8_2_3_1_11326 80 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 195 (accept_3_4 79 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 78 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 195 (accept_3_4 76 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 195 (accept_3_4 73 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 195 (accept_3_4 70 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 195 (accept_3_4 67 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 195 (accept_3_4 64 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 195
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 195 (accept_3_4 61 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 195 (Polychromatic418967fa.accept_21_18_14_6_1_8278 60 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 195 (accept_3_4 58 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 195 (accept_3_4 55 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 195 (accept_3_4 52 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 195 (Polychromatic418967fa.accept_21_9_14_6_1_11308 51 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 195 (accept_3_4 49 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 195 (accept_3_4 46 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 195
  (Polychromatic418967fa.accept_19_6_3_5_1_9897 44 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 195 (accept_3_4 43 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 195 (accept_3_4 40 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 195 (accept_3_4 37 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 195 (Polychromatic418967fa.accept_19_17_3_5_1_3088 36 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 195 (accept_3_4 34 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 195 (accept_3_4 31 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 195 (accept_3_4 28 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 195
  (Polychromatic418967fa.accept_19_7_3_5_1_8585 26 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 195 (accept_3_4 25 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 195 (Polychromatic418967fa.accept_21_3_14_6_1_11325 24 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 195 (accept_3_4 22 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 195 (accept_3_4 19 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 195 (accept_3_4 16 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 195 (Polychromatic418967fa.accept_16_15_2_3_1_4262 15 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 195 (accept_3_4 13 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 195 (accept_3_4 10 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 195
  (Polychromatic418967fa.accept_19_8_3_5_1_11324 8 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 195 (accept_3_4 7 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 98 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 195 (accept_3_4 4 98 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 98 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 98
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 195 (accept_3_4 1 98 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  195 (allA_succ_of_accept 96 97 195 (Polychromatic418967fa.accept_22_8_9_19_1_11323 96 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 195 (accept_3_5 95 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 93 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 97 195 (accept_3_5 92 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  97 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 91 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 195 (accept_3_5 89 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 97 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 195
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 87 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 97 195 (accept_3_5 86 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  97 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 85 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 97 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 84 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 195 (accept_3_5 83 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 195
  (Polychromatic418967fa.accept_12_9_1_3_1_350 81 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 195 (accept_3_5 80 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 195 (Polychromatic418967fa.accept_19_3_2_5_1_5679 79 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 195 (accept_3_5 77 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 75 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 195 (accept_3_5 74 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 195 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 195 (accept_3_5 71 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 195
  (Polychromatic418967fa.accept_12_9_1_3_1_350 69 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 195 (accept_3_5 68 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 195 (accept_3_5 65 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 195
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 195 (accept_3_5 62 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 195 (Polychromatic418967fa.accept_16_13_1_3_1_2205 61 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 195 (Polychromatic418967fa.accept_19_3_2_5_1_5679 60 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 195 (accept_3_5 59 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 195 (accept_3_5 56 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 195 (accept_3_5 53 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 195
  (Polychromatic418967fa.accept_21_9_13_6_1_2285 51 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 195 (accept_3_5 50 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 195 (accept_3_5 47 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 195
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 195 (accept_3_5 44 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 195 (accept_3_5 41 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 195 (accept_3_5 38 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 195 (Polychromatic418967fa.accept_16_4_1_3_1_6581 36 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 195 (accept_3_5 35 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 195
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 195 (accept_3_5 32 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 195 (accept_3_5 29 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 195
  (Polychromatic418967fa.accept_17_10_12_8_1_2748 27 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 195 (accept_3_5 26 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 195 (Polychromatic418967fa.accept_20_5_17_15_1_6858 25 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 195 (Polychromatic418967fa.accept_21_3_13_6_1_11322 24 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 195 (accept_3_5 23 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 195 (accept_3_5 20 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 195 (accept_3_5 17 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 195
  (Polychromatic418967fa.accept_21_15_13_6_1_6659 15 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 195 (accept_3_5 14 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 195 (accept_3_5 11 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 195
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 195 (accept_3_5 8 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  195 (Polychromatic418967fa.accept_19_7_2_5_1_5680 7 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 195 (accept_3_5 5 97 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 195 (accept_3_5 2 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  195 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 97 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 96 195 (allA_succ_of_accept 95 96 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 96 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 94 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 96 195 3 31 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 92 96 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 92 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 195 (Polychromatic418967fa.accept_10_1_6_5_1_304 91 96 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 195 3 30 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 195
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 89 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 96 195 3 29 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 96 195 (Polychromatic418967fa.accept_17_1_11_8_1_2725
  86 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 85 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 195 3 28 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 195 (Polychromatic418967fa.accept_18_11_6_15_1_5953 83 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 96 195 (Polychromatic418967fa.accept_17_14_11_8_1_3854 82 96
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 195 3 27 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 195
  (Polychromatic418967fa.accept_19_4_1_5_1_9933 80 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 96 195 (Polychromatic418967fa.accept_10_9_6_5_1_1002 79 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 195 3 26 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 195 (Polychromatic418967fa.accept_17_9_11_8_1_5077
  77 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 195
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 76 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 96 195 3 25 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 96 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 195 (Polychromatic418967fa.accept_19_16_1_5_1_3084 73 96
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 195 3 24 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 195 (Polychromatic418967fa.accept_17_2_11_8_1_2726 70 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 96 195 3 23 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 96 195 (Polychromatic418967fa.accept_21_5_12_6_1_11321
  68 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 195 3 22 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 195 (Polychromatic418967fa.accept_17_14_11_8_1_3854 65 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 96 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 195 3 21 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 195
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 62 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 195 (Polychromatic418967fa.accept_10_1_6_5_1_304 61 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 195 3 20 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 195 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  59 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 195
  (Polychromatic418967fa.accept_18_4_6_15_1_2250 58 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 96 195 3 19 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 96 195 (Polychromatic418967fa.accept_19_18_1_5_1_5720 56 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 195 (Polychromatic418967fa.accept_22_11_8_19_1_11320 55 96
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 195 3 18 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 195 (Polychromatic418967fa.accept_17_1_11_8_1_2725 52 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 96 195 3 17 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 96 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 195
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 195 3 16 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 195 (Polychromatic418967fa.accept_18_11_6_15_1_5953 47 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 96 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 195 3 15 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 195 3 14 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 195 (Polychromatic418967fa.accept_10_1_6_5_1_304 41
  96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 195
  (Polychromatic418967fa.accept_18_4_6_15_1_2250 40 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 96 195 3 13 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 96 195 (Polychromatic418967fa.accept_20_18_16_15_1_3958 38 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 195 (Polychromatic418967fa.accept_19_18_1_5_1_5720 37 96
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 195 3 12 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 195
  (Polychromatic418967fa.accept_17_1_11_8_1_2725 35 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 96 195 3 11 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 96 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 195
  (Polychromatic418967fa.accept_10_1_6_5_1_304 31 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 195 3 10 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 195 (Polychromatic418967fa.accept_18_10_6_15_1_3412 28 96
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 195 3 9 32 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 195
  (Polychromatic418967fa.accept_17_9_11_8_1_5077 26 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 195 3 8 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 195 (Polychromatic418967fa.accept_18_5_6_15_1_3413 23 96 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 96 195 3 7 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 96 195 (Polychromatic418967fa.accept_14_6_12_13_1_3180 20 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 195 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 96 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 195 3 6 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 195
  (Polychromatic418967fa.accept_18_17_6_15_1_8704 17 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 195 (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 195 3 5 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 96 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 195
  (Polychromatic418967fa.accept_25_13_21_20_1_11319 13 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 96 195 3 4 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 96 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 195
  (Polychromatic418967fa.accept_18_10_6_15_1_3412 10 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 96 195 3 3 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 96 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 195 (Polychromatic418967fa.accept_21_7_12_6_1_3624 7 96 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 195 3 2 32 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 195
  (Polychromatic418967fa.accept_18_5_6_15_1_3413 5 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 96 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 195 3 1 32 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 195 (Polychromatic418967fa.accept_17_2_11_8_1_2726 2 96 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 95 195 (allA_succ_of_accept 94 95 195 (accept_3_4 94 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 95 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 195 (accept_3_4 91 95 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 95 195 5 18 19 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 95 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 89 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 195 (accept_3_4 88 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 95 195 5 17 19 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 95 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 84 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 95 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 83 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 195 (accept_3_4 82 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 95 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 81 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 95 195 5 16 19 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 95 195 (accept_3_4 79 95 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 195 (Polychromatic418967fa.accept_18_6_5_15_1_7292 78 95
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 195
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 77 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 195 (accept_3_4 76 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 95
  195 5 15 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74
  95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 95 195 (accept_3_4 73 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 95 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 71 95 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 95 195 5 14 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 95 195
  (Polychromatic418967fa.accept_12_9_11_3_1_772 69 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 195 (accept_3_4 67 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 95 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 95 195 5 13 19 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 95 195 (accept_3_4 64 95 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 195 (Polychromatic418967fa.accept_17_12_10_8_1_5039 63 95
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 95 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 95 195 (accept_3_4 61 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 95
  195 5 12 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  95 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 95 195 (accept_3_4 58 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 95 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 95 195 5 11 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 95 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 95 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 195 (accept_3_4 52 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 95 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 195 5 10 19 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 195 (accept_3_4 49 95 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 95 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 195 (accept_3_4 46 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 95
  195 5 9 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 95 195 (accept_3_4 43 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 95 195 (Polychromatic418967fa.accept_18_6_5_15_1_7292 42 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 195 (Polychromatic418967fa.accept_21_20_11_6_1_8306 41 95
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 95 195 5 8 19 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 95 195
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 195 (accept_3_4 37 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 95 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 195 5 7 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 195 (accept_3_4 34 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 95 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 195 (accept_3_4 31 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 95
  195 5 6 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  95 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 95 195 (accept_3_4 28 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 95 195 (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 95 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 95 195 5 5 19 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 95 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 95 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 195 (accept_3_4 22 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 95 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 195 5 4 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 195 (accept_3_4 19 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 195 (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 95 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 195 (accept_3_4 16 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 95
  195 5 3 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 95 195 (accept_3_4 13 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 95 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 95 195 5 2 19 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 95 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 195 (accept_3_4 7 95 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 195 (Polychromatic418967fa.accept_18_6_5_15_1_7292 6 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 195 5 1 19 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 195 (accept_3_4 4 95 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 95 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 195 (accept_3_4 1 95 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 195
  (allA_succ_of_accept 93 94 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 195 (accept_3_5 92 94 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  90 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 195 (accept_3_5 89
  94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 88 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 195 (Polychromatic418967fa.accept_14_3_10_13_1_339 87 94 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 195 (accept_3_5 86 94 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 84
  94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 195 (accept_3_5 83 94
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 195 (Polychromatic418967fa.accept_9_1_4_6_1_5
  82 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 195 (accept_3_5 80 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 78 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 195 (accept_3_5 77 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 76 94 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 75 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 195 (accept_3_5 74 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 195 (accept_3_5 71 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 195 (accept_3_5 68 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 195 (accept_3_5 65 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 195
  (Polychromatic418967fa.accept_18_9_4_15_1_555 63 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 195 (accept_3_5 62 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 195 (accept_3_5 59 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 195 (accept_3_5 56 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 195 (accept_3_5 53 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 94 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 195 (accept_3_5 50 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 195 (accept_3_5 47 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 195 (accept_3_5 44 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 195 (accept_3_5 41 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 195 (Polychromatic418967fa.accept_17_6_9_8_1_6316 40 94 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 195 (accept_3_5 38 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 195 (accept_3_5 35 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 195 (accept_3_5 32 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 195 (accept_3_5 29 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 195
  (Polychromatic418967fa.accept_16_11_14_3_1_3140 27 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 195 (accept_3_5 26 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 195 (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 195 (accept_3_5 23 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 195 (Polychromatic418967fa.accept_23_22_2_11_1_6110 22 94
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 195 (accept_3_5 20 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 195 (accept_3_5 17 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 94 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 195
  (Polychromatic418967fa.accept_21_15_10_6_1_11306 15 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 94 195 (accept_3_5 14 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 94 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 94 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 195 (accept_3_5 11 94 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 10
  94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 195 (accept_3_5 8 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 94 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 195 (accept_3_5 5 94 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 94 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  94 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 195 (accept_3_5 2 94 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 195
  (allA_succ_of_accept 92 93 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 92 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 91 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 195 3 30 31 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 89 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 195 3 29 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 86
  93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 195 3 28 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 195 3 27 31 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 195 3 26 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 195 3 25 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 195 3 24 31 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 195 3 23 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 195 3 22 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 195 3 21 31 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 195 3 20 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 195 3 19 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 195 3 18 31 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 195 3 17 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 195 3 16 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 195 3 15 31 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 195 3 14 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 195 3 13 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 195 3 12 31 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 195 3 11 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 195 3 10 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 195 3 9 31 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 195 3 8 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 195 3 7 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 195 3 6 31 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 195 3 5 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 195 3 4 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 195 3 3 31 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 195 3 2 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 93 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 195 3 1 31 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 93 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 195
  (allA_succ_of_accept 91 92 195 (accept_3_4 91 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 195 (accept_3_4 88 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 87 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 195 (accept_3_4 85 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 195 (accept_3_4 82 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 195 (Polychromatic418967fa.accept_22_15_4_19_1_1958 81 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 80 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 195 (accept_3_4 79 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 78 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 195 (accept_3_4 76 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 195
  (Polychromatic418967fa.accept_16_10_12_3_1_4252 74 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 195 (accept_3_4 73 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 195 (accept_3_4 70 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 195 (Polychromatic418967fa.accept_17_1_7_8_1_6347 69 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 195 (accept_3_4 67 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 195 (accept_3_4 64 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 195 (accept_3_4 61 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 195 (Polychromatic418967fa.accept_19_3_16_5_1_7098 60 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 195 (accept_3_4 58 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 195
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 195 (accept_3_4 55 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 195 (accept_3_4 52 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 195 (accept_3_4 49 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 195 (accept_3_4 46 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 195 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 195 (accept_3_4 43 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 195 (accept_3_4 40 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 195 (accept_3_4 37 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 195 (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 195 (accept_3_4 34 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 195 (accept_3_4 31 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 195 (accept_3_4 28 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 195 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 195 (accept_3_4 25 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 195 (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 195 (accept_3_4 22 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 195
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 20 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 195 (accept_3_4 19 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 195 (accept_3_4 16 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 195 (accept_3_4 13 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 195 (accept_3_4 10 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 195 (accept_3_4 7 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 195 (accept_3_4 4 92 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 92 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  92 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 195 (accept_3_4 1 92 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 195
  (allA_succ_of_accept 90 91 195 (Polychromatic418967fa.accept_14_6_7_13_1_3158 90 91 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 195 (accept_3_5 89 91 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 195 (Polychromatic418967fa.accept_16_7_11_3_1_1330
  87 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 195 (accept_3_5 86
  91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 195
  (Polychromatic418967fa.accept_9_4_1_6_1_284 85 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 91 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 195 (accept_3_5 83 91 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  81 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 195 (accept_3_5 80
  91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 195
  (Polychromatic418967fa.accept_9_7_1_6_1_261 79 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 91 195 13 6 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 91 195 (accept_3_5 77 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 195 (accept_3_5 74 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 195 (Polychromatic418967fa.accept_20_13_11_15_1_6881 73 91 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 195
  (Polychromatic418967fa.accept_11_6_3_8_1_843 72 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 195 (accept_3_5 71 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 195 (accept_3_5 68 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 91 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 91 195 13 5 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 195 (Polychromatic418967fa.accept_16_15_11_3_1_2179 63 91
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 195 (accept_3_5 62 91 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 61
  91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 195
  (Polychromatic418967fa.accept_11_5_3_8_1_454 60 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 195 (accept_3_5 59 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 195 (accept_3_5 56 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 195 (Polychromatic418967fa.accept_16_7_11_3_1_1330 55 91 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 195
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 195 (accept_3_5 53 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 91
  195 13 4 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  91 195 (Polychromatic418967fa.accept_21_9_7_6_1_8298 51 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 91 195 (accept_3_5 50 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 91 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 91 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 91 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 195 (accept_3_5 47 91 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 46
  91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 195
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 195 (accept_3_5 44 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 195 (Polychromatic418967fa.accept_19_4_15_5_1_3043 42 91 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 195 (accept_3_5 41 91 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 91 195 13 3 7 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 91 195 (accept_3_5 38 91 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 195 (Polychromatic418967fa.accept_21_16_7_6_1_6687
  37 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 195
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 195 (accept_3_5 35 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 195 (accept_3_5 32 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 91 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 195 (accept_3_5 29 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 91 195 13 2 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 91 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 25
  91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 195
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 195 (accept_3_5 23 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 195 (accept_3_5 20 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 91 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 195
  (Polychromatic418967fa.accept_21_18_7_6_1_3609 18 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 195 (accept_3_5 17 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 195 (accept_3_5 14 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 13 91 195 13 1 7 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 12 91 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 195 (accept_3_5 11 91 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 91 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 195
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 195 (accept_3_5 8 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  195 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 91 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 195 (accept_3_5 5 91 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 195 (accept_3_5 2 91 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 1
  91 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 195
  (allA_succ_of_accept 89 90 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 88 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 195 3 29 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 86 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 90 195 5 17 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 90 195 3 28 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 195 (Polychromatic418967fa.accept_20_3_10_15_1_620 83 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 82 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 90 195 3 27 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 90 195 5 16 18 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 195
  (Polychromatic418967fa.accept_19_3_14_5_1_8597 79 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 195 3 26 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 90 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 195 15 5 6 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 74 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 90 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 195 3 24 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 71
  90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 195 5 14 18 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 90 195 3 23 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 195
  (Polychromatic418967fa.accept_12_8_6_3_1_366 68 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 195 (Polychromatic418967fa.accept_19_10_14_5_1_3079 67 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 195 3 22 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 90 195 5 13 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 90 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 64
  90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 90 195 3 21 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 90 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 62 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 90 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 195 15 4 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 195 (Polychromatic418967fa.accept_19_2_14_5_1_5715 59 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 58 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 90 195 3 19 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 90 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 90 195 5 11 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 195 3 18 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 195
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 90 195 3 17 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 90 195 5 10 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 195 3 16 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 195 (Polychromatic418967fa.accept_14_5_6_13_1_3145
  47 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 195 15 3 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 195 (Polychromatic418967fa.accept_20_3_10_15_1_620 43 90
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 195 3 14 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 195 5 8 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 90 195 3 13 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 90 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 38 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 195 3 12 30 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 195 5 7 18 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 90 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 90 195 3 11 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 90 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 195 (Polychromatic418967fa.accept_20_11_10_15_1_11318 31 90
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 195 15 2 6 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 90 195 3 9 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 90 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 90 195 5 5 18 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 195 3 8 30 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 195
  (Polychromatic418967fa.accept_16_7_10_3_1_2210 23 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 195 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 195 3 7 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 195 5 4 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 195 (Polychromatic418967fa.accept_14_5_6_13_1_3145 19 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 195 3 6 30 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 195 15 1 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 195 3 4 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 195 (Polychromatic418967fa.accept_19_11_14_5_1_5629 11 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 195 5 2 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 195 3 3 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 90 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 195
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 7 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 195 3 2 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 90 195 5 1 18 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 90 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 90 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 195 3 1 30 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 90 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 195 (allA_succ_of_accept 88 89 195 (accept_3_4 88 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 195 (Polychromatic418967fa.accept_16_7_9_3_1_1324 87 89 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 195 (accept_3_4 85 89 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 84
  89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 83 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 195 (accept_3_4 82 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 195 (accept_3_4 79 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 195 (accept_3_4 76 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 195 (accept_3_4 73 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 195 (Polychromatic418967fa.accept_26_20_11_13_1_11317 72 89 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 195 (accept_3_4 70 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 195 (accept_3_4 67 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 195 (accept_3_4 64 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 195 (Polychromatic418967fa.accept_17_12_4_8_1_5073 63 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 195 (accept_3_4 61 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 195 (accept_3_4 58 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 195 (accept_3_4 55 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 195 (accept_3_4 52 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 195 (accept_3_4 49 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 195 (accept_3_4 46 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 195 (accept_3_4 43 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 195 (accept_3_4 40 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 195 (accept_3_4 37 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 195
  (Polychromatic418967fa.accept_17_1_4_8_1_5049 35 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 195 (accept_3_4 34 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 195 (accept_3_4 31 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 195 (accept_3_4 28 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 195 (Polychromatic418967fa.accept_18_9_17_15_1_2267 27 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 195 (accept_3_4 25 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 195 (accept_3_4 22 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 195 (accept_3_4 19 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 195
  (Polychromatic418967fa.accept_25_17_14_20_1_11316 17 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 89 195 (accept_3_4 16 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 89 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 89 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 195 (accept_3_4 13 89 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 195 (accept_3_4 10 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 195 (accept_3_4 7 89 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 195 (accept_3_4 4 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 89 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 195 (accept_3_4 1 89 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 195 (allA_succ_of_accept 87 88 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 195 (accept_3_5 86 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 84 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 88 195 (accept_3_5 83 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  88 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 88 195 (Polychromatic418967fa.accept_17_13_3_8_1_6310 81 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 195 (accept_3_5 80 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 78 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 195 (accept_3_5 77 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 76 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 195 (accept_3_5 74 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 195 (accept_3_5 71 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 195 (Polychromatic418967fa.accept_19_13_12_5_1_9943 70 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 195 (Polychromatic418967fa.accept_16_5_8_3_1_4240 69 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 195 (accept_3_5 68 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 195 (accept_3_5 65 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 195 (accept_3_5 62 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 195
  (Polychromatic418967fa.accept_16_12_8_3_1_4241 60 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 195 (accept_3_5 59 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 195 (accept_3_5 56 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 195 (accept_3_5 53 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 195 (accept_3_5 50 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 195 (accept_3_5 47 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 195 (accept_3_5 44 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 195
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 195 (accept_3_5 41 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 195 (accept_3_5 38 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 195
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 195 (accept_3_5 35 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 195 (Polychromatic418967fa.accept_19_15_12_5_1_8544 34 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 195 (accept_3_5 32 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 195 (accept_3_5 29 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 195 (accept_3_5 26 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 195 (accept_3_5 23 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 195 (accept_3_5 20 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 195 (accept_3_5 17 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 195 (Polychromatic418967fa.accept_19_15_12_5_1_8544 15 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 195 (accept_3_5 14 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 195 (accept_3_5 11 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 195 (accept_3_5 8 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 195 (accept_3_5 5 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  195 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 88 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 88 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 195 (accept_3_5 2 88 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 195
  (allA_succ_of_accept 86 87 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 195 (Polychromatic418967fa.accept_20_5_7_15_1_2668 85 87
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 195 3 28 29 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 195
  (Polychromatic418967fa.accept_10_3_7_5_1_288 83 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 195 (Polychromatic418967fa.accept_10_2_7_5_1_605 82 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 195 3 27 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 195 (Polychromatic418967fa.accept_14_10_3_13_1_1530
  80 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 195 3 26 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 195 (Polychromatic418967fa.accept_21_14_3_6_1_8231 77 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 87 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 195 3 25 29 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 195 3 24 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 195
  (Polychromatic418967fa.accept_19_14_11_5_1_11302 71 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 87 195 (Polychromatic418967fa.accept_19_13_11_5_1_5692 70 87 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 87 195 3 23 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 87 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 68 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 195 3 22 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 87
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 195
  (Polychromatic418967fa.accept_11_9_10_8_1_444 64 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 87 195 3 21 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 87 195 (Polychromatic418967fa.accept_10_2_7_5_1_605 62 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 195 (Polychromatic418967fa.accept_17_10_2_8_1_6295 61 87
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 87 195 3 20 29 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 87 195
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 59 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 87 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 195 3 19 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 195 (Polychromatic418967fa.accept_21_14_3_6_1_8231
  56 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 195
  (Polychromatic418967fa.accept_19_17_11_5_1_7092 55 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 87 195 3 18 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 87 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 87 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 87 195 3 17 29 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 87 195
  (Polychromatic418967fa.accept_17_16_2_8_1_7625 50 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 195 (Polychromatic418967fa.accept_21_7_3_6_1_8322 49 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 195 3 16 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 195 (Polychromatic418967fa.accept_16_15_7_3_1_4273
  47 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 46 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 87 195 3 15 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 87 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 87 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 195 3 14 29 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 195
  (Polychromatic418967fa.accept_16_9_7_3_1_614 41 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 195 (Polychromatic418967fa.accept_21_19_3_6_1_2281 40 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 195 3 13 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 195 (Polychromatic418967fa.accept_10_8_7_5_1_602 38
  87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 87 195 3 12 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 87 195 (Polychromatic418967fa.accept_19_16_11_5_1_11315 35 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 195 (Polychromatic418967fa.accept_19_15_11_5_1_5713 34 87
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 195 3 11 29 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 195 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 195 3 10 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 195 (Polychromatic418967fa.accept_19_10_11_5_1_7093
  29 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 87 195 3 9 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 87 195 (Polychromatic418967fa.accept_16_10_7_3_1_6601 26 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 87 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 195 3 8 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 195 (Polychromatic418967fa.accept_10_2_7_5_1_605 22 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 195 3 7 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 87 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 195
  (Polychromatic418967fa.accept_21_19_3_6_1_2281 19 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 87 195 3 6 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 87 195 (Polychromatic418967fa.accept_19_17_11_5_1_7092 17 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 87 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 195 3 5 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 195
  (Polychromatic418967fa.accept_19_14_11_5_1_11302 14 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 87 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 87 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 195 3 4 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 11
  87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 195
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 10 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 87 195 3 3 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 87 195 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 195 (Polychromatic418967fa.accept_21_7_3_6_1_8322 7 87 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 195 3 2 29 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 195
  (Polychromatic418967fa.accept_20_5_7_15_1_2668 5 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 87 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 195 3 1 29 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 195
  (Polychromatic418967fa.accept_20_1_7_15_1_1521 1 87 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 87 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86
  195 (allA_succ_of_accept 85 86 195 (accept_3_4 85 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 86 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 195 (accept_3_4 82 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 195 (accept_3_4 79 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 195 (accept_3_4 76 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 195 (accept_3_4 73 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 195 (Polychromatic418967fa.accept_17_4_1_8_1_5070 72 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 195 (accept_3_4 70 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 195
  (Polychromatic418967fa.accept_16_4_6_3_1_1311 68 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 195 (accept_3_4 67 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 195 (accept_3_4 64 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 195 (Polychromatic418967fa.accept_24_15_14_3_1_9615 63 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 195 (accept_3_4 61 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 195 (accept_3_4 58 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 195 (accept_3_4 55 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 195 (accept_3_4 52 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 195 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 195 (accept_3_4 49 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 195 (accept_3_4 46 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 195 (accept_3_4 43 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 195 (accept_3_4 40 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 195 (accept_3_4 37 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 195 (accept_3_4 34 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 195 (accept_3_4 31 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 195 (accept_3_4 28 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 195 (Polychromatic418967fa.accept_16_11_6_3_1_6564 27 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 195 (accept_3_4 25 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 195 (accept_3_4 22 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 195 (accept_3_4 19 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 195 (accept_3_4 16 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 195 (accept_3_4 13 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 195 (accept_3_4 10 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 195 (accept_3_4 7 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 195 (accept_3_4 4 86 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  86 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 195 (accept_3_4 1 86 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 195
  (allA_succ_of_accept 84 85 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 84 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 195 (accept_3_5 83 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 195 (Polychromatic418967fa.accept_12_9_1_3_1_350
  81 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 85 195 5 16 17 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 85 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 195 (accept_3_5 77 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 85 195 5 15 17 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 85 195 (accept_3_5 74 85 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 73 85 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 195 (accept_3_5 71 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 85
  195 5 14 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  85 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 85 195 (accept_3_5 68 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 85 195 (Polychromatic418967fa.accept_20_7_5_15_1_1548 67 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 85 195 5 13 17 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 85 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 85 195 (Polychromatic418967fa.accept_14_7_1_13_1_357 63 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 195 (accept_3_5 62 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 85 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 195 5 12 17 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 195 (accept_3_5 59 85 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 195 (accept_3_5 56 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 85
  195 5 11 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  85 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 85 195 (accept_3_5 53 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 85 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 85 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 85 195 5 10 17 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 85 195
  (Polychromatic418967fa.accept_14_7_1_13_1_357 49 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 195 (accept_3_5 47 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 195 5 9 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 195 (accept_3_5 44 85 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 85 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 195 (accept_3_5 41 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 85
  195 5 8 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  85 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 85 195 (accept_3_5 38 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 85 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 195 (Polychromatic418967fa.accept_20_16_5_15_1_5364 36 85
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 85 195 5 7 17 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 85 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 195 (accept_3_5 32 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 195 (Polychromatic418967fa.accept_19_12_9_5_1_8593 31 85 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 195 5 6 17 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 195 (accept_3_5 29 85 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 195
  (Polychromatic418967fa.accept_20_7_5_15_1_1548 27 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 195 (accept_3_5 26 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85
  195 5 5 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  85 195 (Polychromatic418967fa.accept_16_8_5_3_1_4297 24 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 85 195 (accept_3_5 23 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 85 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 195 5 4 17 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 195 (accept_3_5 17 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 195 5 3 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 195 (accept_3_5 14 85 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 195 (Polychromatic418967fa.accept_19_13_9_5_1_8541 13 85 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 195 (accept_3_5 11 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  195 5 2 17 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 195 (accept_3_5 8 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 195 5 1 17 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 195 (accept_3_5 2 85 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 195
  (allA_succ_of_accept 83 84 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 195 3 27 28 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 195 3 26 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 84 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 84 195 3 25 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 84 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 195 3 24 28 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 71 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 195 3 23 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 195 3 22 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 195 3 21 28 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 84 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 195 3 20 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 84 195 3 19 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 84 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 195 3 18 28 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 195 3 17 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 195 3 16 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 195 3 15 28 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 195 3 14 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 84 195 3 13 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 84 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 195 3 12 28 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 195 3 11 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 195 3 10 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 195 3 9 28 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 195 3 8 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 195 3 7 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 195 3 6 28 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 195 3 5 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 195 3 4 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 195 3 3 28 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 195 3 2 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 84 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 84 195 3 1 28 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 84 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 84 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 195
  (allA_succ_of_accept 82 83 195 (accept_3_4 82 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 195 (accept_3_4 79 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 195 (Polychromatic418967fa.accept_10_8_3_5_1_613 78 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 77 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 195 (accept_3_4 76 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 195 (accept_3_4 73 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 195 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 71 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 195 (accept_3_4 70 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 195 (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 195 (accept_3_4 67 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 195
  (Polychromatic418967fa.accept_20_5_3_15_1_6909 65 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 195 (accept_3_4 64 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 195 (Polychromatic418967fa.accept_18_9_11_15_1_4616 63 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 195 (accept_3_4 61 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 195 (Polychromatic418967fa.accept_18_6_11_15_1_7255 60 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 195 (accept_3_4 58 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 195 (accept_3_4 55 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 195 (Polychromatic418967fa.accept_26_2_5_13_1_11314 54 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 195 (accept_3_4 52 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 195 (Polychromatic418967fa.accept_19_13_7_5_1_5712 51 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 195 (accept_3_4 49 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 195
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 195 (accept_3_4 46 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 195 (accept_3_4 43 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 195 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 195 (accept_3_4 40 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 195 (accept_3_4 37 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 195 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 195 (accept_3_4 34 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 195 (accept_3_4 31 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 195
  (Polychromatic418967fa.accept_19_10_7_5_1_5653 29 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 195 (accept_3_4 28 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 195 (accept_3_4 25 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 195 (Polychromatic418967fa.accept_18_6_11_15_1_7255 24 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 195 (accept_3_4 22 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 195 (accept_3_4 19 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 195 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 195 (accept_3_4 16 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 195 (Polychromatic418967fa.accept_21_15_20_6_1_6625 15 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 195 (accept_3_4 13 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 195
  (Polychromatic418967fa.accept_21_11_20_6_1_6641 11 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 195 (accept_3_4 10 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 195 (accept_3_4 7 83 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 195 (Polychromatic418967fa.accept_17_6_15_8_1_1714 6 83 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 195 (accept_3_4 4 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 83 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 195 (accept_3_4 1 83 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 195 (allA_succ_of_accept 81 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 195 (accept_3_5 80 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 82 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 82 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 82 195 (accept_3_5 77 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  82 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 82 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 195 (accept_3_5 74 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 195
  (Polychromatic418967fa.accept_19_15_6_5_1_4356 72 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 195 (accept_3_5 71 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 195 (accept_3_5 68 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 195 (accept_3_5 65 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 195 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 195 (accept_3_5 62 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 195 (accept_3_5 59 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 195 (accept_3_5 56 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 195 (accept_3_5 53 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 195 (Polychromatic418967fa.accept_26_25_4_13_1_11313 51 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 195 (accept_3_5 50 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 195 (accept_3_5 47 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 195 (accept_3_5 44 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 195 (accept_3_5 41 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 195 (accept_3_5 38 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 195 (accept_3_5 35 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 195 (accept_3_5 32 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 195 (accept_3_5 29 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 195 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 195 (accept_3_5 26 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 195
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 195 (accept_3_5 23 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 195 (accept_3_5 20 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 195 (accept_3_5 17 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 195 (accept_3_5 14 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 195 (accept_3_5 11 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 195 (Polychromatic418967fa.accept_20_10_2_15_1_1517 10 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 195 (accept_3_5 8 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 195 (accept_3_5 5 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 82 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 82 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 195 (accept_3_5 2 82 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 195
  (allA_succ_of_accept 80 81 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 195 3 26 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 195
  (Polychromatic418967fa.accept_12_5_9_3_1_85 77 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 76 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 195 3 25 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 195 3 24 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 71 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 195 3 23 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 195 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 195 3 22 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 65
  81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 195
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 64 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 195 3 21 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 195 3 20 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 195 3 19 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024
  56 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 195 3 18 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 195 3 17 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 195 3 16 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 195 3 15 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 195 3 14 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 195
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 195 3 13 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 195 3 12 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 195 3 11 27 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 195
  (Polychromatic418967fa.accept_17_15_13_8_1_7603 32 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 195 3 10 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 29
  81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 195
  (Polychromatic418967fa.accept_18_10_9_15_1_7267 28 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 195 3 9 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 195 3 8 27 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 195 3 7 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 195 (Polychromatic418967fa.accept_16_4_1_3_1_6581 20 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 195 3 6 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 195 3 5 27 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 195 3 4 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 195 3 3 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 195 (Polychromatic418967fa.accept_23_8_12_11_1_11312 8 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 195 3 2 27 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 81 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 195 3 1 27 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 195
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 81 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 195
  (allA_succ_of_accept 79 80 195 (accept_3_4 79 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 195 (accept_3_4 76 80 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 75 80 195 5 15 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 80 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 74 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 80 195 (accept_3_4 73 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 80 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 72
  80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 80 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 195 5 14 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 195 (Polychromatic418967fa.accept_19_12_4_5_1_9936 69 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 68 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 80 195 (accept_3_4 67 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 80 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 66
  80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 80 195 5 13 16 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 80 195 (accept_3_4 64
  80 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 195
  (Polychromatic418967fa.accept_19_6_4_5_1_5650 63 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 80 195 (Polychromatic418967fa.accept_25_12_5_20_1_11311 62 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 80 195 (accept_3_4 61 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 80 195 5 12 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 80 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 195 (accept_3_4 58 80 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 80 195 5 11 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 80 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 80 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 195 (accept_3_4 52 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 51
  80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 195 5 10 16 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 195 (accept_3_4 49
  80 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 80 195
  (Polychromatic418967fa.accept_9_3_8_6_1_80 48 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 80 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 195 (accept_3_4 46 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 80 195 5 9 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 80 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 80 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 80 195 (accept_3_4 43 80 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 80 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 80 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 80 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 195 5 8 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 195 (accept_3_4 37 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 80 195
  (Polychromatic418967fa.accept_21_15_17_6_1_6661 36 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 80 195 5 7 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 80 195 (accept_3_4 34 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  80 195 (Polychromatic418967fa.accept_21_12_17_6_1_8284 33 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 80 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 80 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 195 (accept_3_4 31 80 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 195 5 6 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 80 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 195 (accept_3_4 28 80 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 195
  (Polychromatic418967fa.accept_24_2_8_3_1_7844 26 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 80 195 5 5 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 80 195 (Polychromatic418967fa.accept_22_2_14_19_1_11310 24 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 195 (accept_3_4 22 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 195 5 4 16 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 195 (accept_3_4 19
  80 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 80 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 195 (accept_3_4 16 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 80 195 5 3 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 80 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 80 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 195 (accept_3_4 13 80 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 80 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 195 5 2 16 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 195 (Polychromatic418967fa.accept_19_8_4_5_1_8569 8 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 195 (accept_3_4 7 80 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 195 (Polychromatic418967fa.accept_11_6_3_8_1_843 6
  80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 195 5 1 16 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 195 (accept_3_4 4 80
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 195 (Polychromatic418967fa.accept_9_3_8_6_1_80
  3 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 195 (accept_3_4 1 80 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 195
  (allA_succ_of_accept 78 79 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 79 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 195 (accept_3_5 77 79 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 75
  79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 195 (accept_3_5 74 79
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 195 (Polychromatic418967fa.accept_7_3_2_6_1_56
  73 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 195
  (Polychromatic418967fa.accept_21_9_16_6_1_5134 72 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 195 (accept_3_5 71 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 195 (accept_3_5 68 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 195 (accept_3_5 65 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 195 (Polychromatic418967fa.accept_19_6_3_5_1_9897 63 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 195 (accept_3_5 62 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 61 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 195 (accept_3_5 59 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 195 (accept_3_5 56 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 195
  (Polychromatic418967fa.accept_10_4_9_5_1_84 54 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 195 (accept_3_5 53 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 195 (accept_3_5 50 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 195 (accept_3_5 47 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 195 (accept_3_5 44 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 195
  (Polychromatic418967fa.accept_26_16_1_13_1_11309 42 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 79 195 (accept_3_5 41 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 79 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 195 (accept_3_5 38 79 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 37
  79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 195 (accept_3_5 35 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 195 (accept_3_5 32 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 195 (accept_3_5 29 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 195 (accept_3_5 26 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 195 (accept_3_5 23 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 195 (accept_3_5 20 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 195 (accept_3_5 17 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 195 (accept_3_5 14 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 195 (accept_3_5 11 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 195 (accept_3_5 8 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 195 (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 79 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 195
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 195 (accept_3_5 5 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 195 (accept_3_5 2 79 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 195
  (allA_succ_of_accept 77 78 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 195 3 25 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 74 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 195 3 24 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 195 (Polychromatic418967fa.accept_18_17_6_15_1_8704
  71 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 195
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 70 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 195 3 23 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 67 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 195 3 22 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 78 195 13 5 6 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 78 195
  (Polychromatic418967fa.accept_12_4_6_3_1_332 64 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 78 195 3 21 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 78 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 62 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 195 3 20 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 195
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 59 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 195 3 19 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 56
  78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 195
  (Polychromatic418967fa.accept_19_17_2_5_1_7085 55 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 195 3 18 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 78 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 195 13 4 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 78 195 3 17 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 78 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 195 3 16 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 195 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 195 3 15 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 78 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 43 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 195 3 14 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 40 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 78 195 39 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 78 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 195 3 12 26 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 195
  (Polychromatic418967fa.accept_14_7_8_13_1_3161 35 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 195 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 78 195 3 11 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 78 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 32
  78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 195
  (Polychromatic418967fa.accept_21_10_15_6_1_5090 31 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 195 3 10 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 195 3 9 26 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 195 13 2 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 195 3 8 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 195 3 7 26 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 195
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 195 3 6 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 195 3 5 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 78 195 13 1 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 78 195 3 4 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 195 (Polychromatic418967fa.accept_16_11_14_3_1_3140 11 78
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 78 195 3 3 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 78 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 195 3 2 26 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 195 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 78 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 195 3 1 26 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 78 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 195
  (allA_succ_of_accept 76 77 195 (accept_3_4 76 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 195 (accept_3_4 73 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 195 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 195 (accept_3_4 70 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 195 (accept_3_4 67 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 195 (accept_3_4 64 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 195 (accept_3_4 61 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 195 (Polychromatic418967fa.accept_18_6_5_15_1_7292 60 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 195
  (Polychromatic418967fa.accept_20_19_17_15_1_2690 59 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 77 195 (accept_3_4 58 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 77 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 77 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 195 (accept_3_4 55 77 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 195 (accept_3_4 52 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 195 (Polychromatic418967fa.accept_21_9_14_6_1_11308 51 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 195 (accept_3_4 49 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 195 (accept_3_4 46 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 195 (accept_3_4 43 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 195
  (Polychromatic418967fa.accept_19_3_1_5_1_8549 41 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 195 (accept_3_4 40 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 195 (accept_3_4 37 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 195 (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 195 (accept_3_4 34 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 195 (accept_3_4 31 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 195 (accept_3_4 28 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 195 (Polychromatic418967fa.accept_18_9_5_15_1_2246 27 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 195 (accept_3_4 25 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 195 (Polychromatic418967fa.accept_16_8_13_3_1_4253 24 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 195
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 195 (accept_3_4 22 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 195 (accept_3_4 19 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 195 (accept_3_4 16 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 195 (accept_3_4 13 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 195 (accept_3_4 10 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 195 (accept_3_4 7 77 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 195
  (Polychromatic418967fa.accept_20_5_17_15_1_6858 5 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 195 (accept_3_4 4 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 195 (accept_3_4 1 77 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 195 (allA_succ_of_accept 75 76 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 195 (accept_3_5 74 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 195
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 72 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 195 (accept_3_5 71 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 195 (Polychromatic418967fa.accept_10_9_6_5_1_1002 69 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 195 (accept_3_5 68 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 66 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 195 (accept_3_5 65 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 195 (accept_3_5 62 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 195
  (Polychromatic418967fa.accept_18_6_4_15_1_2276 60 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 195 (accept_3_5 59 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 195 (Polychromatic418967fa.accept_16_10_12_3_1_4252 58 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 195 (accept_3_5 56 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 195 (accept_3_5 53 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 195 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 195 (accept_3_5 50 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 195 (accept_3_5 47 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 195 (Polychromatic418967fa.accept_18_9_4_15_1_555 45 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 195 (accept_3_5 44 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 195
  (Polychromatic418967fa.accept_11_9_10_8_1_444 42 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 195 (accept_3_5 41 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 195 (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 195 (accept_3_5 38 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 195
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 195 (accept_3_5 35 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 195 (Polychromatic418967fa.accept_14_5_6_13_1_3145 33 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 195 (accept_3_5 32 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 195 (accept_3_5 29 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 195 (Polychromatic418967fa.accept_18_9_4_15_1_555 27 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 195 (accept_3_5 26 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 195 (accept_3_5 23 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 195 (Polychromatic418967fa.accept_23_22_7_11_1_7954 22 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 195 (accept_3_5 20 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 195 (accept_3_5 17 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 195 (accept_3_5 14 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 195 (accept_3_5 11 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 195 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 195 (accept_3_5 8 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 195 (accept_3_5 5 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  195 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 76 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 76 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 195 (accept_3_5 2 76 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 195 (allA_succ_of_accept
  74 75 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 75 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 195 3 24 25 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 75 195 5 14 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 75 195 3 23 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 75 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 68 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 75 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 75 195 3 22 25 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 75 195 5 13 15 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 64 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 75 195 3 21 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 75 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 62 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 75 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 195 15 4 5 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 75 195 3 19 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 75 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 195 5 11 15 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 75 195 3 18 25 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 195 3 17 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 75 195 5 10 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 49
  75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 195 3 16 25 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 195 15 3 5 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 75 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 75 195 3 14 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 195 5 8 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 75 195 3 13 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 75 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 195 3 12 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 75 195 5 7 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 195 3 11 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 195 15 2 5 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 195 3 9 25 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 75 195 5 5 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 75 195 3 8 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 75 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 195 3 7 25 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 75 195 5 4 15 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 195 3 6 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 75 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 195 15 1 5 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 195 3 4 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 75 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 195 5 2 15 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 75 195 3 3 25 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 195 3 2 25 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 75 195 5 1 15 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 75 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 195 3 1 25 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 75 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 75 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 195 (allA_succ_of_accept
  73 74 195 (accept_3_4 73 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 74 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 195 (accept_3_4 70 74 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 68
  74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 195 (accept_3_4 67 74
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 195 (accept_3_4 64 74 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 195 (Polychromatic418967fa.accept_23_17_5_11_1_6227 63 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 195 (accept_3_4 61 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 195 (Polychromatic418967fa.accept_16_12_10_3_1_4209 60 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 195 (accept_3_4 58 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 195
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 195 (accept_3_4 55 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 195 (accept_3_4 52 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 195 (accept_3_4 49 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 195 (accept_3_4 46 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 195 (accept_3_4 43 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 195 (accept_3_4 40 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 195 (accept_3_4 37 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 195 (accept_3_4 34 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 195 (accept_3_4 31 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 195 (accept_3_4 28 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 195 (Polychromatic418967fa.accept_22_5_8_19_1_11307 27 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 195 (accept_3_4 25 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 195 (accept_3_4 22 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 195
  (Polychromatic418967fa.accept_21_20_11_6_1_8306 20 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 195 (accept_3_4 19 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 195 (accept_3_4 16 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 195 (Polychromatic418967fa.accept_17_15_6_8_1_6343 15 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 195 (accept_3_4 13 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 195 (accept_3_4 10 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 195 (accept_3_4 7 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  195 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 195 (accept_3_4 4 74 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 74 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  74 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 195 (accept_3_4 1 74 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 195 (allA_succ_of_accept
  72 73 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 195 (accept_3_5 71 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 73 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 195 (accept_3_5 68 73 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 67
  73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 195 (accept_3_5 65 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 195 (Polychromatic418967fa.accept_17_12_5_8_1_7680 63 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 195 (accept_3_5 62 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 73 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 195 (accept_3_5 59 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 195 (accept_3_5 56 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 195 (Polychromatic418967fa.accept_16_7_9_3_1_1324 55 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 195 (accept_3_5 53 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 195 (accept_3_5 50 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 195 (accept_3_5 47 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 195 (accept_3_5 44 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 195 (accept_3_5 41 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 195 (accept_3_5 38 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 195
  (Polychromatic418967fa.accept_21_15_10_6_1_11306 36 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 73 195 (accept_3_5 35 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 73 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 73 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 195 (accept_3_5 32 73 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 31
  73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 195 (accept_3_5 29 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 195 (accept_3_5 26 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 195
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 195 (accept_3_5 23 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 195 (accept_3_5 20 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 195 (Polychromatic418967fa.accept_24_19_1_3_1_9676 19 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 195 (accept_3_5 17 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 195 (accept_3_5 14 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 195 (accept_3_5 11 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 195 (accept_3_5 8 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 195 (accept_3_5 5 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 195 (accept_3_5 2 73 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 195 (Polychromatic418967fa.accept_19_1_16_5_1_5671 1 73 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 195 (allA_succ_of_accept 71
  72 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 195 (Polychromatic418967fa.accept_20_10_12_15_1_3940 70 72 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 195 3 23 24 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 68 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 195 3 22 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 195 (Polychromatic418967fa.accept_20_5_12_15_1_9860
  65 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 64 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 195 3 21 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 195 (Polychromatic418967fa.accept_21_20_9_6_1_11288 62 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 195 (Polychromatic418967fa.accept_16_13_8_3_1_5374 61 72
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 195 3 20 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 195 3 19 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 195 (Polychromatic418967fa.accept_21_14_9_6_1_11289
  56 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 195
  (Polychromatic418967fa.accept_19_17_15_5_1_7096 55 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 195 3 18 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 72 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 195 3 17 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 195 (Polychromatic418967fa.accept_19_11_15_5_1_5699 49 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 195 3 16 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 195 (Polychromatic418967fa.accept_10_7_2_5_1_298 47
  72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 46 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 195 3 15 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 195 (Polychromatic418967fa.accept_16_12_8_3_1_4241 44 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 72 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 195 3 14 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 195
  (Polychromatic418967fa.accept_17_7_4_8_1_7678 41 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 195 (Polychromatic418967fa.accept_25_15_22_20_1_11305 40 72 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 195 3 13 24 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 72 195 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 195 3 12 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 195 (Polychromatic418967fa.accept_17_1_4_8_1_5049
  35 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 195
  (Polychromatic418967fa.accept_21_13_9_6_1_1190 34 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 72 195 3 11 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 72 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 195 3 10 24 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 72 195 3 9 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 72 195 (Polychromatic418967fa.accept_20_6_12_15_1_3938 26 72
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 195 3 8 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 195 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 72 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 195 3 7 24 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 195
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 72 195 (Polychromatic418967fa.accept_25_19_22_20_1_11304 19 72 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 195 3 6 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 195
  (Polychromatic418967fa.accept_21_16_9_6_1_8335 16 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 72 195 3 5 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 72 195 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 195 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 72 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 195 3 4 24 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 72 195 3 3 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 72 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 72 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 195
  (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 195 3 2 24 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 195 (Polychromatic418967fa.accept_16_5_8_3_1_4240 5 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 72 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 195 3 1 24 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 195
  (Polychromatic418967fa.accept_21_2_9_6_1_9809 2 72 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 72 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 195 (allA_succ_of_accept 70
  71 195 (accept_3_4 70 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 195
  (Polychromatic418967fa.accept_10_9_1_5_1_594 69 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 195 (accept_3_4 67 71 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 65
  71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 195 (accept_3_4 64 71
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 195
  (Polychromatic418967fa.accept_14_7_1_13_1_357 63 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 71 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 71 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 195 (accept_3_4 61 71 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 71 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 59
  71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 195 (accept_3_4 58 71
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 195 (Polychromatic418967fa.accept_9_3_8_6_1_80
  57 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 195 (accept_3_4 55 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 195 (Polychromatic418967fa.accept_20_13_11_15_1_6881 53 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 195 (accept_3_4 52 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 71 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 195 (accept_3_4 49 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 195 (accept_3_4 46 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 195 (accept_3_4 43 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 195 (Polychromatic418967fa.accept_16_10_7_3_1_6601 42 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 195 (accept_3_4 40 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 195 (accept_3_4 37 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 195 (accept_3_4 34 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 195 (accept_3_4 31 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 195 (accept_3_4 28 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 195 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 195 (accept_3_4 25 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 195 (accept_3_4 22 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 195 (accept_3_4 19 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 195 (Polychromatic418967fa.accept_26_18_19_13_1_789 18 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 195 (Polychromatic418967fa.accept_19_17_14_5_1_8561 17 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 195 (accept_3_4 16 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 195 (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 71
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 195 (accept_3_4 13 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 195 (accept_3_4 10 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 195 (accept_3_4 7 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 71 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 195 (accept_3_4 4 71 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 71 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 71 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 71 195 (accept_3_4 1 71 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 195 (allA_succ_of_accept 69
  70 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 70 195 (accept_3_5 68 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 70 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 66 70 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 70 195 5 13 14 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 70 195
  (Polychromatic418967fa.accept_9_1_7_6_1_75 64 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 70 195 (Polychromatic418967fa.accept_18_9_16_15_1_2241 63 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 195 (accept_3_5 62 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 70 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 195 5 12 14 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 195 (accept_3_5 59 70 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 70 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 195 (accept_3_5 56 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 70
  195 5 11 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  70 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 70 195 (accept_3_5 53 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 70 195 (Polychromatic418967fa.accept_16_4_6_3_1_1311 52 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 70 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 195 5 10 14 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 70 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 195 (accept_3_5 47 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 70 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 70 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 70 195 5 9 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 70 195 (accept_3_5 44 70 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 70 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 195 (accept_3_5 41 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  195 5 8 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 70 195 (accept_3_5 38 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 70 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 195 (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 70 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 70 195 5 7 14 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 70 195
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 70 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 195 (accept_3_5 32 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 70 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 70 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 195 5 6 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 195 (accept_3_5 29 70 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 70 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 195
  (Polychromatic418967fa.accept_16_11_6_3_1_6564 27 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 195 (accept_3_5 26 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 70
  195 5 5 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  70 195 (Polychromatic418967fa.accept_18_6_16_15_1_7287 24 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 70 195 (accept_3_5 23 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 70 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 195 5 4 14 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 70 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 195 (accept_3_5 17 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 70 195 (Polychromatic418967fa.accept_17_16_2_8_1_7625 16 70 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 70 195 5 3 14 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 70 195 (accept_3_5 14 70 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 195 (accept_3_5 11 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  195 5 2 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 195 (accept_3_5 8 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 70 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 70 195 5 1 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 70 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 70 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 195 (accept_3_5 2 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 195
  (allA_succ_of_accept 68 69 195 (Polychromatic418967fa.accept_19_11_12_5_1_7124 68 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 195 3 22 23 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 195
  (Polychromatic418967fa.accept_12_5_9_3_1_85 65 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 195 3 21 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 195
  (Polychromatic418967fa.accept_10_1_9_5_1_83 61 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 195 3 20 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 59 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 195 3 19 23 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 195
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 55 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 195 3 18 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 53
  69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 195
  (Polychromatic418967fa.accept_25_2_19_20_1_11285 52 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 69 195 3 17 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 69 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 195
  (Polychromatic418967fa.accept_11_5_3_8_1_454 49 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 69 195 3 16 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 69 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 47 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 195 3 15 23 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 195
  (Polychromatic418967fa.accept_10_4_9_5_1_84 44 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 195 3 14 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 41
  69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 195
  (Polychromatic418967fa.accept_16_8_5_3_1_4297 40 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 69 195 3 13 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 69 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 195 3 12 23 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 195
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 195 3 11 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 195 (Polychromatic418967fa.accept_19_13_12_5_1_9943
  32 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 195
  (Polychromatic418967fa.accept_10_1_9_5_1_83 31 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 69 195 3 10 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 69 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 195 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 195 3 9 23 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 195 3 8 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 69 195 3 7 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 69 195 (Polychromatic418967fa.accept_19_1_12_5_1_11303 20 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 195 3 6 23 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 195
  (Polychromatic418967fa.accept_11_6_3_8_1_843 17 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 195 3 5 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 195
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 69 195 3 4 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 69 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 195 3 3 23 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 195
  (Polychromatic418967fa.accept_16_8_5_3_1_4297 8 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 195 3 2 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 195
  (Polychromatic418967fa.accept_10_4_9_5_1_84 4 69 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 69 195 3 1 23 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 69 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 69 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 195 (allA_succ_of_accept 67 68
  195 (accept_3_4 67 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 195
  (Polychromatic418967fa.accept_9_3_5_6_1_253 66 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 195 (accept_3_4 64 68 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 62
  68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 195 (accept_3_4 61 68
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 195 (accept_3_4 58 68 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 56
  68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 195 (accept_3_4 55 68
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 195
  (Polychromatic418967fa.accept_12_6_8_3_1_82 54 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 195 (accept_3_4 52 68 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 195 (Polychromatic418967fa.accept_19_13_11_5_1_5692 51 68 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 195 (accept_3_4 49 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 195 (accept_3_4 46 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 195 (Polychromatic418967fa.accept_20_5_8_15_1_9845 45 68 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 195 (accept_3_4 43 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 195 (accept_3_4 40 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 68 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 195 (accept_3_4 37 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 195 (accept_3_4 34 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 68 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 195 (accept_3_4 31 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 195 (accept_3_4 28 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 68 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 195 (accept_3_4 25 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 195 (Polychromatic418967fa.accept_16_8_4_3_1_3146 24 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 195 (accept_3_4 22 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 195 (accept_3_4 19 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 195 (accept_3_4 16 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 195
  (Polychromatic418967fa.accept_19_14_11_5_1_11302 14 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 68 195 (accept_3_4 13 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 68 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 68 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 195 (accept_3_4 10 68 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 195
  (Polychromatic418967fa.accept_26_9_16_13_1_11301 9 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 68 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 68 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 195 (accept_3_4 7 68 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 68 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 68 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 195 (accept_3_4 4 68 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 68 195 (accept_3_4 1 68 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 195 (allA_succ_of_accept 66 67
  195 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 195 (accept_3_5 65 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 195 (accept_3_5 62 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 195
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 60 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 195 (accept_3_5 59 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 195 (accept_3_5 56 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 195 (accept_3_5 53 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 195 (accept_3_5 50 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 195 (Polychromatic418967fa.accept_19_11_10_5_1_5662 49 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 195 (accept_3_5 47 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 195 (accept_3_5 44 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 195
  (Polychromatic418967fa.accept_10_2_7_5_1_605 42 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 195 (accept_3_5 41 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 195 (accept_3_5 38 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 195
  (Polychromatic418967fa.accept_17_2_16_8_1_3881 36 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 195 (accept_3_5 35 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 195 (accept_3_5 32 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 195 (accept_3_5 29 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 195 (Polychromatic418967fa.accept_19_8_10_5_1_9903 27 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 195 (accept_3_5 26 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 67 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 195 (accept_3_5 23 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 195 (accept_3_5 20 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 195
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 195 (accept_3_5 17 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 195 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 195 (accept_3_5 14 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 195 (accept_3_5 11 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 195 (accept_3_5 8 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 195
  (Polychromatic418967fa.accept_26_6_15_13_1_11300 6 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 195 (accept_3_5 5 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 67 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 195 (accept_3_5 2 67 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 67 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 195 (allA_succ_of_accept 65 66
  195 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 195 3 21 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 62
  66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 195 3 20 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 59 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 195 3 19 22 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 195 3 18 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 195 3 17 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 195 3 16 22 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 195 3 15 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 66
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 195 3 14 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 195 3 13 22 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 195 3 12 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 195 3 11 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 195 3 10 22 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 195 3 9 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 195 3 8 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 195 3 7 22 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 195 3 6 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 195 3 5 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 195 3 4 22 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 195 3 3 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 195 3 2 22 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 66 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 195 3 1 22 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 66 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 195 (allA_succ_of_accept 64 65 195 (accept_3_4 64 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 195 (Polychromatic418967fa.accept_18_9_11_15_1_4616 63 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 195 (accept_3_4 61 65 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 65 195 5 12 13 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 65 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 195 (accept_3_4 58 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 65 195 5 11 13 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 65 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 65 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 65 195 13 4 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 65 195 (Polychromatic418967fa.accept_19_13_8_5_1_8539 51 65 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 195 5 10 13 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 195 (accept_3_4 49
  65 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 195
  (Polychromatic418967fa.accept_9_3_2_6_1_264 48 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 195 (Polychromatic418967fa.accept_20_7_5_15_1_1548 47 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 195 (accept_3_4 46 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 195 5 9 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 195 (accept_3_4 43 65 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 195 5 8 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 65 195 13 3 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 65 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 195 (accept_3_4 37 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 195 5 7 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 195 (accept_3_4 34 65 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 65 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 195 (accept_3_4 31 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 65
  195 5 6 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  65 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 65 195 (accept_3_4 28 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 65 195 (Polychromatic418967fa.accept_18_9_11_15_1_4616 27 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 65 195 13 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 65 195 5 5 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 65 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 195 (accept_3_4 22 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 65 195 5 4 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 65 195 (accept_3_4 19 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 65 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 195 (accept_3_4 16 65 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 65 195 5 3 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 65 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 65 195 13 1 5 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 65 195
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 65 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 65 195 5 2 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 65 195 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 65 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 195 (accept_3_4 7 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 65 195 5 1 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 65 195 (accept_3_4 4 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 65 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 195 (accept_3_4 1 65 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 195
  (allA_succ_of_accept 63 64 195 (Polychromatic418967fa.accept_14_7_8_13_1_3161 63 64 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 195 (accept_3_5 62 64 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 195
  (Polychromatic418967fa.accept_18_6_10_15_1_9963 60 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 64 195 (accept_3_5 59 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  64 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 64 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 195 (accept_3_5 56 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 64 195 (accept_3_5 53 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  64 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 64 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 195 (accept_3_5 50 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 64 195 (accept_3_5 47 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  64 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 64 195 (Polychromatic418967fa.accept_18_9_10_15_1_7254 45 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 195 (accept_3_5 44 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 64 195 (accept_3_5 41 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  64 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 64 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 195 (accept_3_5 38 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 195
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 195 (accept_3_5 35 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 195 (accept_3_5 32 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 195 (accept_3_5 29 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 195 (Polychromatic418967fa.accept_19_9_7_5_1_9887 28 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 195 (Polychromatic418967fa.accept_18_9_10_15_1_7254 27 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 195 (accept_3_5 26 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 195
  (Polychromatic418967fa.accept_18_6_10_15_1_9963 24 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 195 (accept_3_5 23 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 195 (accept_3_5 20 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 195 (accept_3_5 17 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 195 (Polychromatic418967fa.accept_17_15_13_8_1_7603 15 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 195 (accept_3_5 14 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 195 (accept_3_5 11 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 195 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 195 (accept_3_5 8 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 195
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 195 (accept_3_5 5 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  195 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 64 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 64 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 195 (accept_3_5 2 64 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 195 (allA_succ_of_accept 62 63 195
  (Polychromatic418967fa.accept_10_2_3_5_1_996 62 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 195 (Polychromatic418967fa.accept_16_13_15_3_1_4196 61 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 195 3 20 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 195 (Polychromatic418967fa.accept_16_11_15_3_1_1304
  59 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 195
  (Polychromatic418967fa.accept_10_8_3_5_1_613 58 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 195 3 19 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 195 (Polychromatic418967fa.accept_17_5_12_8_1_6304 56 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 195 (Polychromatic418967fa.accept_16_7_15_3_1_1302 55 63
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 195 3 18 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 195
  (Polychromatic418967fa.accept_18_17_9_15_1_7268 53 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 195 3 17 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 195 (Polychromatic418967fa.accept_14_8_7_13_1_4113
  50 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 195
  (Polychromatic418967fa.accept_19_11_6_5_1_11299 49 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 195 3 16 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 195 (Polychromatic418967fa.accept_18_10_9_15_1_7267 46 63
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 195 3 15 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 44 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 43 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 195 3 14 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 195 (Polychromatic418967fa.accept_18_5_9_15_1_4695
  41 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 195
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 40 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 195 3 13 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 195 (Polychromatic418967fa.accept_10_8_3_5_1_613 38 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 195 3 12 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 195
  (Polychromatic418967fa.accept_18_17_9_15_1_7268 35 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 195 (Polychromatic418967fa.accept_14_6_7_13_1_3158 34 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 195 3 11 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 195 (Polychromatic418967fa.accept_10_2_3_5_1_996 32
  63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 195
  (Polychromatic418967fa.accept_25_6_13_20_1_11298 31 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 63 195 3 10 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 63 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 29 63 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 195 3 9 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 195 (Polychromatic418967fa.accept_19_7_6_5_1_4320 26 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 195 (Polychromatic418967fa.accept_20_5_3_15_1_6909 25 63
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 195 3 8 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 195
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 23 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 195 (Polychromatic418967fa.accept_10_2_3_5_1_996 22 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 195 3 7 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 63 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 195
  (Polychromatic418967fa.accept_23_19_17_11_1_11297 19 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 63 195 3 6 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 63 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 195
  (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 195 3 5 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 63 195 (Polychromatic418967fa.accept_19_14_6_5_1_9917 14 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 195 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 63
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 195 3 4 21 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 195
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 195 (Polychromatic418967fa.accept_17_10_12_8_1_2748 10 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 195 3 3 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 195 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 63 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 195
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 195 3 2 21 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 195 (Polychromatic418967fa.accept_17_5_12_8_1_6304 5 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 63 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 195 3 1 21 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 195
  (Polychromatic418967fa.accept_10_2_3_5_1_996 2 63 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 63 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 62 195 (allA_succ_of_accept 61 62 195 (accept_3_4 61 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 62 195 (Polychromatic418967fa.accept_17_9_11_8_1_5077 60 62 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 62 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 62 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 195 (accept_3_4 58 62 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 62 195 (accept_3_4 55 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  62 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 195 (accept_3_4 52 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 195 (Polychromatic418967fa.accept_21_9_20_6_1_9815 51 62 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 195 (accept_3_4 49 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 195 (accept_3_4 46 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 195
  (Polychromatic418967fa.accept_20_4_2_15_1_6904 44 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 195 (accept_3_4 43 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 195 (accept_3_4 40 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 62 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 195 (accept_3_4 37 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 195 (Polychromatic418967fa.accept_17_2_11_8_1_2726 36 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 195 (accept_3_4 34 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 195 (accept_3_4 31 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 195 (accept_3_4 28 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 195 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 62 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 195
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 195 (accept_3_4 25 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 195 (Polychromatic418967fa.accept_20_4_2_15_1_6904 24 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 195 (accept_3_4 22 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 195 (accept_3_4 19 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 195 (accept_3_4 16 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 62 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 195 (accept_3_4 13 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 195 (accept_3_4 10 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 195 (accept_3_4 7 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 62 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 195 (accept_3_4 4 62 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 62 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 62
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 195 (accept_3_4 1 62 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 195 (allA_succ_of_accept 60 61 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 195 (accept_3_5 59 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 195 (accept_3_5 56 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 195 (accept_3_5 53 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 195 (Polychromatic418967fa.accept_22_7_17_19_1_11296 51 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 195 (accept_3_5 50 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 61 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 195 (accept_3_5 47 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 195 (accept_3_5 44 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 195 (accept_3_5 41 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 195 (accept_3_5 38 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 195 (accept_3_5 35 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 195 (accept_3_5 32 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 195 (accept_3_5 29 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 195 (Polychromatic418967fa.accept_19_8_4_5_1_8569 27 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 195 (accept_3_5 26 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 195
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 195 (accept_3_5 23 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 195 (accept_3_5 20 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 195 (accept_3_5 17 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 195 (accept_3_5 14 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 195 (accept_3_5 11 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 195 (accept_3_5 8 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 195 (Polychromatic418967fa.accept_20_7_1_15_1_2700 7 61 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 195 (accept_3_5 5 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 195 (accept_3_5 2 61 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 195 (allA_succ_of_accept 59 60 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 58 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 195 3 19 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 195 (Polychromatic418967fa.accept_16_8_12_3_1_4194 56 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 195 5 11 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 195 3 18 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 195 (Polychromatic418967fa.accept_18_17_6_15_1_8704
  53 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 52 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 60 195 3 17 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 60 195 5 10 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 195 (Polychromatic418967fa.accept_21_7_18_6_1_9797 49 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 195 3 16 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 195
  (Polychromatic418967fa.accept_11_2_5_8_1_470 46 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 60 195 15 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 60 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 195 (Polychromatic418967fa.accept_22_21_16_19_1_11295 43 60
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 195 3 14 20 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 195
  (Polychromatic418967fa.accept_16_9_12_3_1_3138 41 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 195 5 8 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 60 195 3 13 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 195 3 12 20 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 195 5 7 12 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 195
  (Polychromatic418967fa.accept_18_16_6_15_1_3376 34 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 60 195 3 11 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 60 195 (Polychromatic418967fa.accept_21_11_18_6_1_3521 32 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 195 15 2 4 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 195
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 29 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 195 (Polychromatic418967fa.accept_17_11_9_8_1_5038 28 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 195 3 9 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 60 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 195 5 5 12 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 195 3 8 20 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 195 (Polychromatic418967fa.accept_18_4_6_15_1_2250 22 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 195 3 7 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 195 5 4 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 195 3 6 20 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 195 15 1 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 195 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 60 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 195
  (Polychromatic418967fa.accept_11_2_5_8_1_470 13 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 195 3 4 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 195 (Polychromatic418967fa.accept_17_11_9_8_1_5038 11 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 195 5 2 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 195 3 3 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 195 (Polychromatic418967fa.accept_16_8_12_3_1_4194 8 60 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 195 3 2 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 60 195 5 1 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 60 195 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 60 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 195 3 1 20 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 60 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 195
  (Polychromatic418967fa.accept_17_1_9_8_1_7492 1 60 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 195 (allA_succ_of_accept 58
  59 195 (accept_3_4 58 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 195
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 195 (accept_3_4 55 59 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 53
  59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 195 (accept_3_4 52 59
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 195 (Polychromatic418967fa.accept_7_2_3_6_1_4
  51 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 195 (accept_3_4 49 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 195 (accept_3_4 46 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 195 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 59 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 195 (accept_3_4 43 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 195 (Polychromatic418967fa.accept_18_6_5_15_1_7292 42 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 195 (accept_3_4 40 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 59 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 195 (accept_3_4 37 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 195 (accept_3_4 34 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 59 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 195 (accept_3_4 31 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 195 (accept_3_4 28 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 195 (Polychromatic418967fa.accept_18_9_5_15_1_2246 27 59 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 195 (accept_3_4 25 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 195 (accept_3_4 22 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 195 (accept_3_4 19 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 195 (accept_3_4 16 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 195 (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 59 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 195 (accept_3_4 13 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 195 (accept_3_4 10 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 59 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 195 (accept_3_4 7 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 59 195 (Polychromatic418967fa.accept_20_5_19_15_1_3946 5 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 195 (accept_3_4 4 59 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 195 (accept_3_4 1 59 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 195 (allA_succ_of_accept 57 58 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 195 (accept_3_5 56 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 58 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 195 (accept_3_5 53 58 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 58 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 195
  (Polychromatic418967fa.accept_21_9_16_6_1_5134 51 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 195 (accept_3_5 50 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 195 (accept_3_5 47 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 58 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 195 (accept_3_5 44 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 195 (accept_3_5 41 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 195 (Polychromatic418967fa.accept_24_16_10_3_1_11294 40 58 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 195 (accept_3_5 38 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 195 (accept_3_5 35 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 58 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 195 (accept_3_5 32 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 195 (accept_3_5 29 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 58 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 195
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 195 (accept_3_5 26 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 195 (accept_3_5 23 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 58 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 195 (accept_3_5 20 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 195 (accept_3_5 17 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 58 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 195 (accept_3_5 14 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 195 (accept_3_5 11 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 58 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 195 (accept_3_5 8 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 195 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 58 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 195 (accept_3_5 5 58 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 58 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 58
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 195 (accept_3_5 2 58 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 195 (allA_succ_of_accept 56 57 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 195 3 18 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 195 3 17 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 195 3 16 19 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 195 3 15 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 195 3 14 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 57 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 195 3 13 19 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 195 3 12 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 195 3 11 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 57 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 195 3 10 19 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 195 3 9 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 195 3 8 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 195 3 7 19 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 195 3 6 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 57 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 195 3 5 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 195 3 4 19 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 195 3 3 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 195 3 2 19 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 57 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 195 3 1 19 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 195 (allA_succ_of_accept 55 56 195 (accept_3_4 55 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 195 (accept_3_4 52 56 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 195 (Polychromatic418967fa.accept_10_1_6_5_1_304
  51 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 195 (accept_3_4 49 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 195 (accept_3_4 46 56 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 195 (Polychromatic418967fa.accept_16_13_8_3_1_5374 45 56 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 195 (accept_3_4 43 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 195 (accept_3_4 40 56 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 195
  (Polychromatic418967fa.accept_20_18_16_15_1_3958 38 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 56 195 (accept_3_4 37 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 56 195 (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 56 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 195 (accept_3_4 34 56 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 195
  (Polychromatic418967fa.accept_21_12_14_6_1_8214 33 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 56 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 195 (accept_3_4 31 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 56 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 56 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 29
  56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 195 (accept_3_4 28 56
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 195
  (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 56 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 195 (accept_3_4 25 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 56 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 56 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 195 (accept_3_4 22 56
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 195
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 56 195 (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 195 (accept_3_4 19 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 56 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 56 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 195 (accept_3_4 16 56
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 195
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 56 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 195 (accept_3_4 13 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 56 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 56 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 195 (accept_3_4 10 56
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 195
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 56 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 195 (accept_3_4 7 56 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 56 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 195 (accept_3_4 4 56 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 195
  (Polychromatic418967fa.accept_19_2_18_5_1_11293 2 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 195 (accept_3_4 1 56 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 195 (allA_succ_of_accept 54 55 195
  (Polychromatic418967fa.accept_22_10_11_19_1_11292 54 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 55 195 (accept_3_5 53 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 55 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 195 (Polychromatic418967fa.accept_21_9_13_6_1_2285 51 55
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 195 5 10 11 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 195
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 195 (accept_3_5 47 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 55 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 195 5 9 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 195 (accept_3_5 44 55 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 55 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 195
  (Polychromatic418967fa.accept_16_10_7_3_1_6601 42 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 195 (accept_3_5 41 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  195 5 8 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 195 (accept_3_5 38 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 195 (Polychromatic418967fa.accept_19_18_17_5_1_4343 37 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 55 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 195 5 7 11 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 34 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 195 (accept_3_5 32 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 55 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 195 5 6 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 195 (accept_3_5 29 55 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 195
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 195 (accept_3_5 26 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  195 5 5 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 195 (Polychromatic418967fa.accept_17_7_4_8_1_7678 24 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 195 (accept_3_5 23 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 195 5 4 11 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 195
  (Polychromatic418967fa.accept_21_19_13_6_1_3550 19 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 195 (Polychromatic418967fa.accept_17_1_4_8_1_5049 18 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 195 (accept_3_5 17 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 195 5 3 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 195 (accept_3_5 14 55 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 195 (accept_3_5 11 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  195 5 2 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 195 (accept_3_5 8 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 195 (Polychromatic418967fa.accept_30_6_25_15_1_11291 6 55
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 195 5 1 11 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 195 (accept_3_5 2 55 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 195 (Polychromatic418967fa.accept_17_1_4_8_1_5049 1 55 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 195 (allA_succ_of_accept 53 54 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 195
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 54 195 3 17 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 54 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 195 3 16 18 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 195
  (Polychromatic418967fa.accept_17_13_3_8_1_6310 47 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 195 3 15 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 44
  54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 195 3 14 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 54 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 195 3 13 18 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 195 3 12 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 195 (Polychromatic418967fa.accept_21_14_12_6_1_8222
  35 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 54 195 3 11 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 54 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 195 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 54 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 195 3 10 18 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 195 3 9 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 195 3 8 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 195 (Polychromatic418967fa.accept_21_2_12_6_1_6658 23 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 54 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 195 3 7 18 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 195
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 195 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 195 3 6 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 195
  (Polychromatic418967fa.accept_10_6_4_5_1_615 16 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 54 195 3 5 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 54 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 195 3 4 18 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 195 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 195 3 3 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 54 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 195
  (Polychromatic418967fa.accept_21_7_12_6_1_3624 7 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 195 3 2 18 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 54 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 195 3 1 18 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 54 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 195)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  195 (allA_succ_of_accept 52 53 195 (accept_3_4 52 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 195 (accept_3_4 49 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 53 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 195 (accept_3_4 46 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 195 (accept_3_4 43 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 195 (accept_3_4 40 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 195 (accept_3_4 37 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 195 (Polychromatic418967fa.accept_19_17_15_5_1_7096 36 53 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 195
  (Polychromatic418967fa.accept_21_14_11_6_1_8305 35 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 195 (accept_3_4 34 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 195 (accept_3_4 31 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 195 (accept_3_4 28 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 195 (accept_3_4 25 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 195 (accept_3_4 22 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 195 (accept_3_4 19 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 195 (accept_3_4 16 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 195 (Polychromatic418967fa.accept_21_15_11_6_1_5121 15 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 195 (accept_3_4 13 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 195 (accept_3_4 10 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 195 (accept_3_4 7 53 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 195 (accept_3_4 4 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 53 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 195 (accept_3_4 1 53 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 195))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 195
  (allA_succ_of_accept 51 52 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 52 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 195 (accept_3_5 50 52 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 48
  52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 195 (accept_3_5 47 52
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 46 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 195 (Polychromatic418967fa.accept_14_3_10_13_1_339 45 52 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 195 (accept_3_5 44 52 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 195 (Polychromatic418967fa.accept_12_6_4_3_1_361
  42 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 195 (accept_3_5 41
  52 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 195
  (Polychromatic418967fa.accept_9_4_7_6_1_255 40 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 52 195 13 3 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 52 195 (accept_3_5 38 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 195 (Polychromatic418967fa.accept_19_17_14_5_1_8561 36 52 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 195 (accept_3_5 35 52 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 195 (Polychromatic418967fa.accept_25_9_2_20_1_3970 34 52
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 195
  (Polychromatic418967fa.accept_10_3_2_5_1_295 33 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 195 (accept_3_5 32 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 52 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 195 (accept_3_5 29 52 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 52 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 195
  (Polychromatic418967fa.accept_10_7_2_5_1_298 27 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 195 13 2 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 195 (Polychromatic418967fa.accept_16_8_4_3_1_3146 24 52 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 195 (accept_3_5 23 52 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 22
  52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 195 (accept_3_5 20 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 52 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 195 (accept_3_5 17 52 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 52 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 195 (accept_3_5 14 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 52
  195 13 1 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12
  52 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 52 195 (accept_3_5 11 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 52 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 52 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 52 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 195 (accept_3_5 8 52 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 195 (accept_3_5 5 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 52 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 195 (accept_3_5 2 52 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 195))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 195 (allA_succ_of_accept 50 51 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 51 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 195
  (Polychromatic418967fa.accept_10_9_1_5_1_594 49 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 51 195 3 16 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 51 195 (Polychromatic418967fa.accept_19_9_13_5_1_4351 47 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 51 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 195 3 15 17 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 195
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 195 3 14 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 195 (Polychromatic418967fa.accept_21_20_9_6_1_11288
  41 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 195
  (Polychromatic418967fa.accept_22_18_7_19_1_11290 40 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 51 195 3 13 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 51 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 51 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 195
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 195 3 12 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 195 (Polychromatic418967fa.accept_21_14_9_6_1_11289 35 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 51 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 195 3 11 17 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 195 3 10 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 29
  51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 195
  (Polychromatic418967fa.accept_19_9_13_5_1_4351 28 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 195 3 9 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 51 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 195 3 8 17 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 195
  (Polychromatic418967fa.accept_21_2_9_6_1_9809 23 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 195 3 7 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 195 (Polychromatic418967fa.accept_21_20_9_6_1_11288 20 51
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 195
  (Polychromatic418967fa.accept_10_9_1_5_1_594 19 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 195 3 6 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 51 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 195 3 5 17 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 195
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 195 (Polychromatic418967fa.accept_20_13_11_15_1_6881 13 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 195 3 4 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 51 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 195 3 3 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 195 (Polychromatic418967fa.accept_19_7_13_5_1_7125 7 51 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 195 3 2 17 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 195
  (Polychromatic418967fa.accept_20_5_11_15_1_3920 5 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 51 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 195 3 1 17 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 195 (Polychromatic418967fa.accept_21_2_9_6_1_9809 2 51 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 51 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 195))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 195 (allA_succ_of_accept 49 50 195
  (accept_3_4 49 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 195
  (Polychromatic418967fa.accept_9_3_5_6_1_253 48 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 195 (accept_3_4 46 50 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 50 195 5 9 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 50 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 50 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 195 (accept_3_4 43 50 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 50 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 50 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 195 5 8 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 50 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 50 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 195 (accept_3_4 37 50 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 195 (Polychromatic418967fa.accept_11_3_6_8_1_1924
  36 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 50 195 5 7 10 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 50 195 (accept_3_4 34
  50 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 50 195 (Polychromatic418967fa.accept_19_13_12_5_1_9943 32 50 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 195 (accept_3_4 31 50 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 50 195 5 6 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 195 (accept_3_4 28 50 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 195 (Polychromatic418967fa.accept_19_8_12_5_1_7122 27 50 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 195 5 5 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 195 (Polychromatic418967fa.accept_17_7_16_8_1_7613 24 50 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 195 (accept_3_4 22 50 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 195 5 4 10 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 195 (accept_3_4 19
  50 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 195
  (Polychromatic418967fa.accept_12_6_2_3_1_354 18 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 195 (accept_3_4 16 50 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 50 195 5 3 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 50 195 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 50 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 195 (accept_3_4 13 50 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 50 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 195 5 2 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 50 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 195 (accept_3_4 7 50 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 195 5 1 10 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 195 (accept_3_4 4 50
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 195 (Polychromatic418967fa.accept_9_3_5_6_1_253
  3 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 195 (accept_3_4 1 50 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  195)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 195 (allA_succ_of_accept 48 49 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 195 (accept_3_5 47 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 195 (accept_3_5 44 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 49 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 195 (accept_3_5 41 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 195 (accept_3_5 38 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 195
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 195 (accept_3_5 35 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 195 (accept_3_5 32 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 195 (accept_3_5 29 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 195 (Polychromatic418967fa.accept_17_10_15_8_1_6324 27 49 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 195 (accept_3_5 26 49 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 195
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 195 (accept_3_5 23 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 195 (accept_3_5 20 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 195 (accept_3_5 17 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 195 (accept_3_5 14 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 49 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 195 (accept_3_5 11 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 195 (accept_3_5 8 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 49 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 195 (accept_3_5 5 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 49 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 195 (accept_3_5 2 49 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 195))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 195 (allA_succ_of_accept 47 48 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 195 3 15 16 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 195 3 14 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 195 3 13 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 48 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 195 3 12 16 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 195 3 11 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 195 3 10 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 48 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 195 3 9 16 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 195 3 8 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 48 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 195 3 7 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 48 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 195 3 6 16 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 195 3 5 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 48 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 195 3 4 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 48 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 195 3 3 16 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 195 3 2 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 48 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 195 3 1 16 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 48 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  195)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 195 (allA_succ_of_accept 46 47 195 (accept_3_4 46 47
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 195
  (Polychromatic418967fa.accept_12_9_11_3_1_772 45 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 195 (accept_3_4 43 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 195 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 47 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 41
  47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 195 (accept_3_4 40 47
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 195 (accept_3_4 37 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 35
  47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 195 (accept_3_4 34 47
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 195
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 195 (accept_3_4 31 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 47 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 195 (accept_3_4 28 47
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 195
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 195 (accept_3_4 25 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 195 (Polychromatic418967fa.accept_18_6_11_15_1_7255 24 47 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 195 (accept_3_4 22 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 195 (accept_3_4 19 47 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 195 (accept_3_4 16 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 195 (accept_3_4 13 47 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 195 (accept_3_4 10 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 195 (accept_3_4 7 47 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 195 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 47 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 195 (accept_3_4 4 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 195 (accept_3_4 1 47 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 195))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 195 (allA_succ_of_accept 45
  46 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 46 195 (accept_3_5 44 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 46 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 46
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 195 (accept_3_5 41 46 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 40
  46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 195 (accept_3_5 38 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 195 (Polychromatic418967fa.accept_21_15_4_6_1_11286 36 46 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 195 (accept_3_5 35 46 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 46 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 195 (accept_3_5 32 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 46 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 195 (accept_3_5 29 46 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 195 (Polychromatic418967fa.accept_21_7_4_6_1_11287 28 46 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 195
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 195 (accept_3_5 26 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 46 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 195 (accept_3_5 23 46 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 46 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 195 (accept_3_5 20 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 46 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 195 (accept_3_5 17 46 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 46 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 195
  (Polychromatic418967fa.accept_21_15_4_6_1_11286 15 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 195 (accept_3_5 14 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 46 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 195 (accept_3_5 11 46 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 46 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 195 (accept_3_5 8 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 46 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 195 (accept_3_5 5 46 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 46 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  46 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 195 (accept_3_5 2 46 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  195)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 195 (allA_succ_of_accept 44 45 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 45 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 195 3 14 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 195 5 8 9 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 45 195 3 13 15 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 45 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 195 3 12 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 45 195 5 7 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 195 3 11 15 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 45 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 195 15 2 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 45 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 195
  (Polychromatic418967fa.accept_18_10_9_15_1_7267 28 45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 195 3 9 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 195 5 5 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 195 3 8 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 45 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 195 3 7 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 45 195 5 4 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 45 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 195 3 6 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 195 15 1 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 45 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 195 3 4 15 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 195 5 2 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 45 195 3 3 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 195 (Polychromatic418967fa.accept_16_8_13_3_1_4253 8 45 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 45 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 195 3 2 15 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 45 195 5 1 9 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 45 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 195 3 1 15 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 45 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  195))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 195 (allA_succ_of_accept 43 44 195 (accept_3_4 43 44
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 195
  (Polychromatic418967fa.accept_12_6_8_3_1_82 42 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 195 (accept_3_4 40 44 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 38
  44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 195 (accept_3_4 37 44
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 195 (Polychromatic418967fa.accept_7_1_2_6_1_55
  36 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 44 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 44 195 (accept_3_4 34 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  44 195 (Polychromatic418967fa.accept_19_14_6_5_1_9917 33 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 44 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 195 (accept_3_4 31 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 44 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 195 (accept_3_4 28 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 195 (Polychromatic418967fa.accept_25_2_19_20_1_11285 27 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 195 (accept_3_4 25 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 44 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 195 (accept_3_4 22 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 195 (accept_3_4 19 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 44 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 195 (accept_3_4 16 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 195 (accept_3_4 13 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 44 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 195 (accept_3_4 10 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 195 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 195 (accept_3_4 7 44 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 44 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 195 (accept_3_4 4 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 44 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 195 (accept_3_4 1 44 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 195)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 195 (allA_succ_of_accept 42 43
  195 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 43 195 (accept_3_5 41 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 43 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 43 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 195 (accept_3_5 38 43 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 37
  43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 195
  (Polychromatic418967fa.accept_21_15_1_6_1_8258 36 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 195 (accept_3_5 35 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 43 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 195 (accept_3_5 32 43 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 43 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 195 (accept_3_5 29 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 43 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 195 (accept_3_5 26 43 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 195 (Polychromatic418967fa.accept_20_5_3_15_1_6909 25 43 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 195
  (Polychromatic418967fa.accept_16_8_11_3_1_4279 24 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 195 (accept_3_5 23 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 195 (accept_3_5 20 43 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 195
  (Polychromatic418967fa.accept_10_8_3_5_1_613 18 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 195 (accept_3_5 17 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 195 (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 43 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 195 (accept_3_5 14 43 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 43 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 195 (accept_3_5 11 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 43 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 195 (accept_3_5 8 43 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 195
  (Polychromatic418967fa.accept_16_6_11_3_1_2198 6 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 195 (accept_3_5 5 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 43 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 195 (accept_3_5 2 43 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 195))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 195
  (allA_succ_of_accept 41 42 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 42 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 195 3 13 14 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 195 3 12 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 195 (Polychromatic418967fa.accept_18_17_6_15_1_8704
  35 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 195 3 11 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 195 (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 195 (Polychromatic418967fa.accept_19_12_4_5_1_9936 31 42
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 195 3 10 14 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 195 3 9 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 42 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 195 3 8 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 195 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 195 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 42 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 195 3 7 14 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 195
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 195 (Polychromatic418967fa.accept_24_19_18_3_1_11284 19 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 195 3 6 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 195
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 195 3 5 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 195 3 4 14 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 195
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 11 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 195 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 195 3 3 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 42 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 195
  (Polychromatic418967fa.accept_10_7_2_5_1_298 7 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 195 3 2 14 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 42 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 195 3 1 14 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 195)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 195
  (allA_succ_of_accept 40 41 195 (accept_3_4 40 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 195 (accept_3_4 37 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 41 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 195 (accept_3_4 34 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 195 (accept_3_4 31 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 195 (accept_3_4 28 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 195 (Polychromatic418967fa.accept_18_9_5_15_1_2246 27 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 195 (accept_3_4 25 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 41 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 195
  (Polychromatic418967fa.accept_16_7_9_3_1_1324 23 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 195 (accept_3_4 22 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 195 (accept_3_4 19 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 195 (accept_3_4 16 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 195 (Polychromatic418967fa.accept_21_15_20_6_1_6625 15 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 195 (accept_3_4 13 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 41 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 195 (accept_3_4 10 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 195 (accept_3_4 7 41 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 195
  (Polychromatic418967fa.accept_20_5_1_15_1_3928 5 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 195 (accept_3_4 4 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 41 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 195 (accept_3_4 1 41 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 195))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 195 (allA_succ_of_accept 39 40 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 195 (accept_3_5 38 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 40 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 195 5 7 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 34
  40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 195
  (Polychromatic418967fa.accept_19_14_2_5_1_9949 33 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 195 (accept_3_5 32 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 40 195 5 6 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 40 195 (accept_3_5 29 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 40 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 40 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 195 (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 40
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 195 (accept_3_5 26 40 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40 195 5 5 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 40 195 (Polychromatic418967fa.accept_18_6_4_15_1_2276
  24 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 195 (accept_3_5 23
  40 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 40 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 195 5 4 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 40 195 (accept_3_5 17 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  40 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 40 195 5 3 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 40 195 (accept_3_5 14 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 40 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 40 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 195 (accept_3_5 11 40 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 195 5 2 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 195 (Polychromatic418967fa.accept_17_9_6_8_1_6315 9
  40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 40 195 (accept_3_5 8 40 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 40 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 40 195 5 1 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 40 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 40 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 40 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 195 (accept_3_5 2 40 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  195)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 195 (allA_succ_of_accept 38 39 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 39 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 195 3 12 13 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 39 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 195 3 11 13 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 39 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 195 3 10 13 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 39 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 39 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 195 3 9 13 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 39 195 13 2 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 195 3 8 13 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 39 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 39 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 195 3 7 13 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 39 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 39 195 3 6 13 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 39 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 39 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 39 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 195 3 5 13 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 39 195 13 1 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 39 195 3 4 13 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 39 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 195 3 3 13 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 39 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 195 3 2 13 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 39 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 39 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 195 3 1 13 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 39 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 39 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 195)))))))))))))))))))))))))))))))))))))))
  (allB_succ 38 195 (allA_succ_of_accept 37 38 195 (accept_3_4 37 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 38 195 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 38 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 38 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 195 (accept_3_4 34 38 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 195 (accept_3_4 31 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 195 (accept_3_4 28 38 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 38 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 195 (accept_3_4 25 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 195 (accept_3_4 22 38 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 195
  (Polychromatic418967fa.accept_16_4_6_3_1_1311 20 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 195 (accept_3_4 19 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 195 (accept_3_4 16 38 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 195 (Polychromatic418967fa.accept_21_15_17_6_1_6661 15 38 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 195 (accept_3_4 13 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 195 (accept_3_4 10 38 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 195 (accept_3_4 7 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 38 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 195 (accept_3_4 4 38 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 38
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 195 (accept_3_4 1 38 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 195)))))))))))))))))))))))))))))))))))))) (allB_succ 37 195
  (allA_succ_of_accept 36 37 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 195 (accept_3_5 35 37 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 195 (Polychromatic418967fa.accept_10_3_7_5_1_288
  33 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 195 (accept_3_5 32
  37 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 195 (accept_3_5 29 37 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 195
  (Polychromatic418967fa.accept_31_27_6_9_1_11283 27 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 195 (accept_3_5 26 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 195 (accept_3_5 23 37 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 195 (accept_3_5 20 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 195 (Polychromatic418967fa.accept_20_19_17_15_1_2690 19 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 195 (accept_3_5 17 37 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 195 (accept_3_5 14 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 37 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 195 (accept_3_5 11 37 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 195
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 195 (accept_3_5 8 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  195 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 37 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 195 (accept_3_5 5 37 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 37
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 195 (accept_3_5 2 37 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 195)))))))))))))))))))))))))))))))))))))
  (allB_succ 36 195 (allA_succ_of_accept 35 36 195 (Polychromatic418967fa.accept_14_7_8_13_1_3161 35 36 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 34 36 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 36 195 3 11 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 36 195 (Polychromatic418967fa.accept_21_11_15_6_1_3667 32 36 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 36 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 195 3 10 12 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 195
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 36 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 195 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 36 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 195 3 9 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 36 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 195
  (Polychromatic418967fa.accept_20_5_16_15_1_3957 25 36 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 195 3 8 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 195 (Polychromatic418967fa.accept_16_6_4_3_1_2189 22 36 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 195 3 7 12 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 195
  (Polychromatic418967fa.accept_21_20_15_6_1_11282 20 36 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 36 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 195 3 6 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 195 (Polychromatic418967fa.accept_11_6_3_8_1_843 17
  36 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 36 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 36 195 3 5 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 36 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 195 (Polychromatic418967fa.accept_21_13_15_6_1_3556 13 36
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 195 3 4 12 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 195
  (Polychromatic418967fa.accept_10_1_6_5_1_304 11 36 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 195 (Polychromatic418967fa.accept_17_10_2_8_1_6295 10 36 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 195 3 3 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 195 (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 36 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 195 3 2 12 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 36 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 195 3 1 12 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 36 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 195 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 195)))))))))))))))))))))))))))))))))))) (allB_succ 35 195
  (allA_succ_of_accept 34 35 195 (accept_3_4 34 35 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 35 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 195 (accept_3_4 31 35 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 35 195 5 6 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 35 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 35 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 195 (accept_3_4 28 35 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 35 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 195 5 5 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 195 (Polychromatic418967fa.accept_17_7_1_8_1_6280 24 35 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 195 (accept_3_4 22 35 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  35 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 195 5 4 7 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 195 (accept_3_4 19
  35 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 195
  (Polychromatic418967fa.accept_21_18_14_6_1_8278 18 35 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 195 (Polychromatic418967fa.accept_22_17_13_19_1_11281 17 35 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 195 (accept_3_4 16 35 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 35 195 5 3 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 35 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 35 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 195 (accept_3_4 13 35 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 195 5 2 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 35 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 195 (accept_3_4 7 35 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 195 (Polychromatic418967fa.accept_14_6_7_13_1_3158
  6 35 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 195 5 1 7 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 195 (accept_3_4 4 35
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 195 (Polychromatic418967fa.accept_9_3_8_6_1_80
  3 35 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 195 (accept_3_4 1 35 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  195))))))))))))))))))))))))))))))))))) (allB_succ 34 195 (allA_succ_of_accept 33 34 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 195 (accept_3_5 32 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 34 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 195 (accept_3_5 29 34 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 34 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 195
  (Polychromatic418967fa.accept_18_9_16_15_1_2241 27 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 195 (accept_3_5 26 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 195 (Polychromatic418967fa.accept_18_6_16_15_1_7287 24 34 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 195 (accept_3_5 23 34 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 34 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 195 (accept_3_5 20 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 34 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 195 (accept_3_5 17 34 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 34 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 195
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 195 (accept_3_5 14 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 34 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 195 (accept_3_5 11 34 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 34 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 195 (accept_3_5 8 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 34 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 195 (accept_3_5 5 34 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 34 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 34
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 195 (accept_3_5 2 34 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 195))))))))))))))))))))))))))))))))))
  (allB_succ 33 195 (allA_succ_of_accept 32 33 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 33 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 195 3 10 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 33 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 195 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 33 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 195 3 9 11 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 195 3 8 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 33 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 195 3 7 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 195 (Polychromatic418967fa.accept_14_6_5_13_1_367 20 33 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 195 3 6 11 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 195
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 33 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 195 (Polychromatic418967fa.accept_19_16_14_5_1_9920 16 33 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 195 3 5 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 195
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 33 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 195 3 4 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 33 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 195 3 3 11 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 33 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 195 3 2 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 33 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 33 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 195 3 1 11 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 195)))))))))))))))))))))))))))))))))
  (allB_succ 32 195 (allA_succ_of_accept 31 32 195 (accept_3_4 31 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 32 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 195 (accept_3_4 28 32 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 195 (Polychromatic418967fa.accept_10_7_2_5_1_298
  27 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 195 (accept_3_4 25 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 195 (accept_3_4 22 32 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 195 (accept_3_4 19 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 195 (accept_3_4 16 32 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 195 (Polychromatic418967fa.accept_21_15_11_6_1_5121 15 32 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 195
  (Polychromatic418967fa.accept_19_14_13_5_1_9905 14 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 195 (accept_3_4 13 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 195 (accept_3_4 10 32 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 195 (accept_3_4 7 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 195 (accept_3_4 4 32 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  32 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 195 (accept_3_4 1 32 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 195)))))))))))))))))))))))))))))))) (allB_succ 31 195
  (allA_succ_of_accept 30 31 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 31 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 195 (accept_3_5 29 31 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 195
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 195 (accept_3_5 26 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 31 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 195 (accept_3_5 23 31 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 195 (accept_3_5 20 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 31 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 195 (accept_3_5 17 31 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 195
  (Polychromatic418967fa.accept_19_15_12_5_1_8544 15 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 195 (accept_3_5 14 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 195 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 195 (accept_3_5 11 31 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 195 (accept_3_5 8 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 31 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 195 (accept_3_5 5 31 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  31 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 195 (accept_3_5 2 31 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 31
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 195)))))))))))))))))))))))))))))))
  (allB_succ 30 195 (allA_succ_of_accept 29 30 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 30 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 30 195 3 9 10 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 30 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 30 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 195 5 5 6 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 195 3 8 10 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 30 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 30 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 195 3 7 10 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 195 5 4 6 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 30 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 195 3 6 10 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 30 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 30 195 15 1 2 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 30 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 30 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 195 3 4 10 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 195 5 2 6 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 30 195 3 3 10 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 30 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 30 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 195 3 2 10 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 195 5 1 6 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 30 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 195 3 1 10 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 30 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 195)))))))))))))))))))))))))))))) (allB_succ
  29 195 (allA_succ_of_accept 28 29 195 (accept_3_4 28 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 195 (Polychromatic418967fa.accept_17_10_12_8_1_2748 27 29 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 195 (accept_3_4 25 29 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 24
  29 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 195 (accept_3_4 22 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 195 (accept_3_4 19 29 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 195 (accept_3_4 16 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 195 (accept_3_4 13 29 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 195
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 195 (accept_3_4 10 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 195 (accept_3_4 7 29 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 195 (accept_3_4 4 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 29 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 195 (accept_3_4 1 29 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 195))))))))))))))))))))))))))))) (allB_succ 28 195 (allA_succ_of_accept 27 28 195
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 195 (accept_3_5 26 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 195 (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 28 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 195 (accept_3_5 23 28 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 28 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 195 (accept_3_5 20 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 195 (accept_3_5 17 28 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 28 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 195 (accept_3_5 14 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 28 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 195 (accept_3_5 11 28 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 195 (Polychromatic418967fa.accept_16_10_12_3_1_4252 10 28 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 195
  (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 195 (accept_3_5 8 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 28 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 195 (accept_3_5 5 28 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 28 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 195 (accept_3_5 2 28 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 195))))))))))))))))))))))))))))
  (allB_succ 27 195 (allA_succ_of_accept 26 27 195 (Polychromatic418967fa.accept_25_1_2_20_1_11280 26 27 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 195
  (Polychromatic418967fa.accept_11_3_5_8_1_458 25 27 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 195 3 8 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 27 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 195 (Polychromatic418967fa.accept_10_2_7_5_1_605 22 27 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 195 3 7 9 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 195
  (Polychromatic418967fa.accept_23_20_4_11_1_2963 20 27 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 195 (Polychromatic418967fa.accept_17_2_10_8_1_7691 19 27 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 195 3 6 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 195 (Polychromatic418967fa.accept_18_17_9_15_1_7268 17 27
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 195
  (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 27 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 195 3 5 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 195 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 27 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 195 3 4 9 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 195
  (Polychromatic418967fa.accept_18_11_9_15_1_5988 11 27 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 195 (Polychromatic418967fa.accept_18_10_9_15_1_7267 10 27 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 195 3 3 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 195 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 27 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 195
  (Polychromatic418967fa.accept_16_7_11_3_1_1330 7 27 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 195 3 2 9 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 195 (Polychromatic418967fa.accept_18_5_9_15_1_4695 5 27 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 195 (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 27 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 195 3 1 9 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 195
  (Polychromatic418967fa.accept_10_2_7_5_1_605 2 27 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 195 (Polychromatic418967fa.accept_20_1_7_15_1_1521 1 27 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 195))))))))))))))))))))))))))) (allB_succ 26 195 (allA_succ_of_accept 25
  26 195 (accept_3_4 25 26 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 26 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 195 (accept_3_4 22 26 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 20
  26 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 195 (accept_3_4 19 26
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 26 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 195 (accept_3_4 16 26 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 26 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 14
  26 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 26 195 13 1 2 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 26 195
  (Polychromatic418967fa.accept_9_3_8_6_1_80 12 26 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 195 (accept_3_4 10 26 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 26
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 195 (accept_3_4 7 26 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  26 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 195 (accept_3_4 4 26 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 26 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 26 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 195 (accept_3_4 1 26 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 195)))))))))))))))))))))))))) (allB_succ 25 195 (allA_succ_of_accept 24 25 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 195 (accept_3_5 23 25 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 195 5 4 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 19
  25 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 195 (accept_3_5 17 25 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 25 195 5 3 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 25 195 (accept_3_5 14 25 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 25 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 25 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 195 (accept_3_5 11 25 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 195 5 2 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 195 (accept_3_5 8 25 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 195 (Polychromatic418967fa.accept_16_7_9_3_1_1324 7
  25 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 195 5 1 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 25 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 195 (accept_3_5 2 25 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 25
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 195))))))))))))))))))))))))) (allB_succ
  24 195 (allA_succ_of_accept 23 24 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 195 (Polychromatic418967fa.accept_18_4_6_15_1_2250 22 24
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 195 3 7 8 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 195
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 24 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 195 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 24 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 195 3 6 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 195 (Polychromatic418967fa.accept_14_3_10_13_1_339 17 24 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 24 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 195 3 5 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 195 (Polychromatic418967fa.accept_17_14_7_8_1_7544 14 24 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 195 (Polychromatic418967fa.accept_16_13_8_3_1_5374 13 24
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 195 3 4 8 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 195 (Polychromatic418967fa.accept_18_10_6_15_1_3412 10 24 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 195 3 3 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 195 (Polychromatic418967fa.accept_21_8_3_6_1_11279 8 24 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 195
  (Polychromatic418967fa.accept_21_7_3_6_1_8322 7 24 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 195 3 2 8 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 24 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 24 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 195 3 1 8 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 24 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 195 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 24 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 195)))))))))))))))))))))))) (allB_succ 23 195 (allA_succ_of_accept 22 23
  195 (accept_3_4 22 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 195
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 195 (accept_3_4 19 23 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  23 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 195 (accept_3_4 16 23
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 195 (Polychromatic418967fa.accept_7_1_2_6_1_55
  15 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 195 (accept_3_4 13 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 195 (accept_3_4 10 23 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 195 (accept_3_4 7 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  195 (Polychromatic418967fa.accept_18_6_5_15_1_7292 6 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 23 195 (Polychromatic418967fa.accept_20_5_3_15_1_6909 5 23 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 195 (accept_3_4 4 23 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 23 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 195 (accept_3_4 1 23 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  195))))))))))))))))))))))) (allB_succ 22 195 (allA_succ_of_accept 21 22 195 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 22 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 195 (accept_3_5 20
  22 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 22 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 22 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 195 (accept_3_5 17 22 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 22 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 22 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 195 (Polychromatic418967fa.accept_21_15_1_6_1_8258
  15 22 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 195 (accept_3_5 14
  22 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 22 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 22 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 195 (accept_3_5 11 22 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 22 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 22 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 195 (accept_3_5 8 22 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 22 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 22 195 (accept_3_5 5 22 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22
  195 (Polychromatic418967fa.accept_16_4_6_3_1_1311 4 22 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 22 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 22 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 195 (accept_3_5 2 22 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 195)))))))))))))))))))))) (allB_succ 21 195
  (allA_succ_of_accept 20 21 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 195 3 6 7 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 195 3 5 7 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 195 3 4 7 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 195 3 3 7 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 21 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 195 3 2 7 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 195 3 1 7 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 195))))))))))))))))))))) (allB_succ 20 195
  (allA_succ_of_accept 19 20 195 (accept_3_4 19 20 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 20 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 195 (accept_3_4 16 20 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 20 195 5 3 4 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 20 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 20 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 195 (accept_3_4 13 20 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 20 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 195 5 2 4 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 195 (Polychromatic418967fa.accept_19_9_1_5_1_11278 9 20 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 20 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 195 (accept_3_4 7 20 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6
  20 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 195 5 1 4 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 195 (accept_3_4 4 20
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 195 (Polychromatic418967fa.accept_9_3_2_6_1_264
  3 20 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 195
  (Polychromatic418967fa.accept_21_2_20_6_1_2277 2 20 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 195 (accept_3_4 1 20 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  195)))))))))))))))))))) (allB_succ 19 195 (allA_succ_of_accept 18 19 195 (Polychromatic418967fa.accept_7_4_5_6_1_344
  18 19 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 195 (accept_3_5 17
  19 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 19 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 195 (accept_3_5 14 19 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 19 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 19 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  19 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 195 (accept_3_5 11 19
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 195 (Polychromatic418967fa.accept_6_4_1_3_1_77
  10 19 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 195
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 19 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 195 (accept_3_5 8 19 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  195 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 19 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 195 (accept_3_5 5 19 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 195 (accept_3_5 2 19 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 195))))))))))))))))))) (allB_succ 18 195
  (allA_succ_of_accept 17 18 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 18 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 195 3 5 6 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 18 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 195 3 4 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 195 (Polychromatic418967fa.accept_17_11_1_8_1_7502 11 18 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 10 18 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 18 195 3 3 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 18 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 18 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 18 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 195 3 2 6 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 18 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 18 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 18 195 3 1 6 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 18 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 18 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 195)))))))))))))))))) (allB_succ 17 195 (allA_succ_of_accept 16 17 195 (accept_3_4 16 17 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 195 (Polychromatic418967fa.accept_19_15_17_5_1_3052 15 17
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 195 (accept_3_4 13 17 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 195 (accept_3_4 10 17 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 17 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 195 (accept_3_4 7 17 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 195 (accept_3_4 4 17 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 195 (accept_3_4 1 17 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 195))))))))))))))))) (allB_succ 16 195 (allA_succ_of_accept 15
  16 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 16 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 16 195 (accept_3_5 14 16 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 16 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 16 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 195 (accept_3_5 11 16 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 10
  16 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 195
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 16 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 195 (accept_3_5 8 16 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 16 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 195 (accept_3_5 5 16 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 16 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 16
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 195 (accept_3_5 2 16 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 195)))))))))))))))) (allB_succ 15 195
  (allA_succ_of_accept 14 15 195 (Polychromatic418967fa.accept_24_14_15_3_1_11277 14 15 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 195 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 15
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 195 3 4 5 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 195
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 15 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 15 195 5 2 3 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 15 195 3 3 5 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 195 (Polychromatic418967fa.accept_21_8_15_6_1_8247 8 15 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 15 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 195 3 2 5 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 195 5 1 3 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 15 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 15 195 3 1 5 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 15 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 15 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 195 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 15 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 195))))))))))))))) (allB_succ 14 195
  (allA_succ_of_accept 13 14 195 (accept_3_4 13 14 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  14 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 14 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 14 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 195 (accept_3_4 10 14 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 14 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 14 195 (accept_3_4 7 14 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14
  195 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 14 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 195 (accept_3_4 4 14 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  14 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 195 (accept_3_4 1 14 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 195)))))))))))))) (allB_succ 13 195 (allA_succ_of_accept 12 13
  195 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 195 (accept_3_5 11 13 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 13 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 195 (accept_3_5 8 13 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 195 (accept_3_5 5 13 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 13 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 195 (accept_3_5 2 13 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 195))))))))))))) (allB_succ 12 195 (allA_succ_of_accept 11 12
  195 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 12 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 195 3 3 4 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 12 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 195 3 2 4 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 12 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 195 3 1 4 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 12 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 195)))))))))))) (allB_succ 11 195 (allA_succ_of_accept 10 11 195
  (accept_3_4 10 11 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 11 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 195 (accept_3_4 7 11 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 11 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  11 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 195 (accept_3_4 4 11 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  11 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 195 (accept_3_4 1 11 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  195))))))))))) (allB_succ 10 195 (allA_succ_of_accept 9 10 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 195 (accept_3_5 8 10 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 10 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 10 195 5 1 2 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 10 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 10 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 195 (accept_3_5 2 10 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 195)))))))))) (allB_succ 9 195
  (allA_succ_of_accept 8 9 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 195 3 2 3 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 195
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 9 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 9 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 195 3 1 3 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 195))))))))) (allB_succ 8 195 (allA_succ_of_accept 7 8 195 (accept_3_4 7 8 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 8 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 195 (accept_3_4 4 8 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 195
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 8 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 8 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 195 (accept_3_4 1 8 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 195)))))))) (allB_succ 7 195 (allA_succ_of_accept 6 7 195
  (Polychromatic418967fa.accept_14_6_7_13_1_3158 6 7 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 195 (accept_3_5 5 7 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 195 (accept_3_5 2 7 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 195))))))) (allB_succ 6 195 (allA_succ_of_accept 5 6 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 6 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 195 3 1 2 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 6 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 195)))))) (allB_succ 5 195 (allA_succ_of_accept 4 5 195 (accept_3_4 4 5 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 5 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 195 (accept_3_4 1 5 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 195))))) (allB_succ 4 195 (allA_succ_of_accept 3 4 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 4 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 195 (accept_3_5 2 4 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 195)))) (allB_succ 3 195 (allA_succ_of_accept 2 3 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 3 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 195))) (allB_succ 2 195 (allA_succ_of_accept 1 2 195 (accept_3_4 1 2 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 195)) (allB_two
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


