-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch225_Segment000
-- name    : Polychromatic418967fa_Branch225_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:33:59.544213+00:00
-- url     : https://prove2.me/theorems/865222b2-ddda-4789-9aaa-c30edc69dabe
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

def Polychromatic418967fa.branch_225_segment_000 : allB 100 225 :=
  allB_succ 99 225 (allA_succ_of_accept 98 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 97 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 225 3 32 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630 95 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 225 3 31 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 225
  (Polychromatic418967fa.accept_17_7_14_4_1_4745 92 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 225 9 10 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 225 (Polychromatic418967fa.accept_12_5_3_9_1_541 89
  99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 225
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 88 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 225 3 29 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 85 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 225 3 28 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 225
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 83 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 225 9 9 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 225 (Polychromatic418967fa.accept_23_11_7_18_1_13430 80 99
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 225
  (Polychromatic418967fa.accept_12_7_3_9_1_999 79 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 225 3 26 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 225 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 225 (Polychromatic418967fa.accept_10_6_9_5_1_1046 76 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 225 3 25 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 225 9 8 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 71 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 225 3 23 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 225 (Polychromatic418967fa.accept_16_4_3_1_1_8843 68 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 67 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 225 3 22 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 225
  (Polychromatic418967fa.accept_12_5_3_9_1_541 65 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 225 9 7 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 61 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 225 3 20 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 225 3 19 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 225
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 225 9 6 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 225 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 225
  (Polychromatic418967fa.accept_16_4_3_1_1_8843 52 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 225 3 17 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 225 3 16 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 225
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 225 9 5 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 44 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 225
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 225 3 14 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 225 (Polychromatic418967fa.accept_19_2_4_16_1_7984 40 99
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 225 3 13 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 225 9 4 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 225 3 11 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 225 (Polychromatic418967fa.accept_24_8_3_9_1_11731 32 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 225 3 10 33 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 225
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 225 (Polychromatic418967fa.accept_19_9_4_16_1_2586 28 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 225 9 3 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 225 3 8 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 225 3 7 33 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 225
  (Polychromatic418967fa.accept_16_4_3_1_1_8843 20 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 225 9 2 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 225 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 225
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 225 3 5 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 225 3 4 33 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 225 9 1 11 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 225 (Polychromatic418967fa.accept_24_8_3_9_1_11731 8 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 225
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 225 3 2 33 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 225 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 99 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 225 3 1 33 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  225 (allA_succ_of_accept 97 98 225 (accept_3_4 97 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 225 (Polychromatic418967fa.accept_18_6_8_9_1_1960 96 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 225 (accept_3_4 94 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 93 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 92 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 225 (accept_3_4 91 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 90 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 225 (accept_3_4 88 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 225
  (Polychromatic418967fa.accept_16_6_2_1_1_4081 86 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 225 (accept_3_4 85 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 225 (Polychromatic418967fa.accept_13_6_7_4_1_2264 84 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 225 (accept_3_4 82 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 225 (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 225
  (Polychromatic418967fa.accept_19_4_3_16_1_5097 80 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 225 (accept_3_4 79 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 225 (accept_3_4 76 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 225
  (Polychromatic418967fa.accept_13_9_7_4_1_953 74 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 225 (accept_3_4 73 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 225 (accept_3_4 70 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 225 (Polychromatic418967fa.accept_24_21_2_9_1_9974 69 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 225
  (Polychromatic418967fa.accept_13_3_7_4_1_435 68 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 225 (accept_3_4 67 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 225 (accept_3_4 64 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 225 (accept_3_4 61 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 225 (Polychromatic418967fa.accept_16_12_2_1_1_1215 60 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 225 (accept_3_4 58 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 225 (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 225
  (Polychromatic418967fa.accept_19_18_3_16_1_7962 56 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 225 (accept_3_4 55 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 225 (accept_3_4 52 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 225
  (Polychromatic418967fa.accept_11_6_10_5_1_341 50 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 225 (accept_3_4 49 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 225 (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 225 (accept_3_4 46 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 225 (Polychromatic418967fa.accept_13_6_7_4_1_2264 45 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 225
  (Polychromatic418967fa.accept_16_12_2_1_1_1215 44 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 225 (accept_3_4 43 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 225 (accept_3_4 40 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 225
  (Polychromatic418967fa.accept_13_12_7_4_1_3124 38 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 225 (accept_3_4 37 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 225 (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 225 (accept_3_4 34 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 225 (accept_3_4 31 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 225 (accept_3_4 28 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 225
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 225 (accept_3_4 25 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 225 (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 225 (accept_3_4 22 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 225 (Polychromatic418967fa.accept_18_3_8_9_1_1956 21 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 225
  (Polychromatic418967fa.accept_17_3_13_4_1_8530 20 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 225 (accept_3_4 19 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 225 (accept_3_4 16 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 225
  (Polychromatic418967fa.accept_17_14_13_4_1_13402 14 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 98 225 (accept_3_4 13 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 98 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 98 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 225 (accept_3_4 10 98 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 225 (Polychromatic418967fa.accept_13_9_7_4_1_953 9
  98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 225
  (Polychromatic418967fa.accept_17_8_13_4_1_6012 8 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 225 (accept_3_4 7 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  225 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 98 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 225 (accept_3_4 4 98 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 225 (accept_3_4 1 98 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  225 (allA_succ_of_accept 96 97 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 225 (accept_3_5 95 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 93
  97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 225 (accept_3_5 92 97
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 225
  (Polychromatic418967fa.accept_14_7_13_1_1_922 91 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 97 225 (Polychromatic418967fa.accept_19_14_2_16_1_6484 90 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 225 (accept_3_5 89 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 225 (Polychromatic418967fa.accept_12_3_1_9_1_202
  87 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 225 (accept_3_5 86
  97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 225
  (Polychromatic418967fa.accept_13_7_6_4_1_933 85 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 97 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 84 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 225 (accept_3_5 83 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 225 (Polychromatic418967fa.accept_19_5_2_16_1_8013
  81 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 225 (accept_3_5 80
  97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 79 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 97 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 78 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 225 (accept_3_5 77 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 75
  97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 225 (accept_3_5 74 97
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 225
  (Polychromatic418967fa.accept_10_3_7_5_1_288 73 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 97 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 225 (accept_3_5 71 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 225
  (Polychromatic418967fa.accept_21_6_13_15_1_11870 69 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 97 225 (accept_3_5 68 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 97 225 (Polychromatic418967fa.accept_13_2_6_4_1_1593 67 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 225 (Polychromatic418967fa.accept_30_6_7_15_1_6915 66 97
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 225 (accept_3_5 65 97 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 64
  97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 225
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 225 (accept_3_5 62 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 225 (Polychromatic418967fa.accept_17_9_12_4_1_3468 60 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 225 (accept_3_5 59 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 97 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 225
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 57 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 225 (accept_3_5 56 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 225 (Polychromatic418967fa.accept_19_17_2_16_1_7982 55 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 225 (accept_3_5 53 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 225 (accept_3_5 50 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 225 (Polychromatic418967fa.accept_13_10_6_4_1_1583 49 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 225 (accept_3_5 47 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 225
  (Polychromatic418967fa.accept_19_7_2_16_1_1496 45 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 225 (accept_3_5 44 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 225 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 225 (accept_3_5 41 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 225
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 225 (accept_3_5 38 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 225 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 225 (accept_3_5 35 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 97 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 225 (accept_3_5 32 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 225 (Polychromatic418967fa.accept_13_5_6_4_1_1582 31 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 225 (accept_3_5 29 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 225
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 225 (accept_3_5 26 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 225 (Polychromatic418967fa.accept_17_8_12_4_1_2525 25 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 225 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 225 (accept_3_5 23 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 97 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 225
  (Polychromatic418967fa.accept_14_7_13_1_1_922 21 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 225 (accept_3_5 20 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 225 (accept_3_5 17 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 225
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 225 (accept_3_5 14 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 225 (accept_3_5 11 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 225 (accept_3_5 8 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  225 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 225 (Polychromatic418967fa.accept_18_6_7_9_1_4250 6 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 225 (accept_3_5 5 97 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 3
  97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 225 (accept_3_5 2 97 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 225 (Polychromatic418967fa.accept_22_1_9_5_1_10410
  1 97 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 225
  (allA_succ_of_accept 95 96 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 94 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 96 225 3 31 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 96 225
  (Polychromatic418967fa.accept_13_1_5_4_1_463 92 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 96 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 91 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 225 3 30 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 225 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  89 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 88 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 96 225 3 29 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 96 225 (Polychromatic418967fa.accept_18_14_6_9_1_1950 86 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 225 (Polychromatic418967fa.accept_18_13_6_9_1_4280 85 96
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 225 3 28 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 83 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 225 (Polychromatic418967fa.accept_21_19_12_15_1_7307 82 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 225 3 27 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 80
  96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 225
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 79 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 225 3 26 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 225 (Polychromatic418967fa.accept_13_12_5_4_1_3133 77 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 76 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 96 225 3 25 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 96 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 96 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 225 3 24 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 71
  96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 225
  (Polychromatic418967fa.accept_19_13_1_16_1_7979 70 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 96 225 3 23 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 96 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219 68 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 225 3 22 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 225
  (Polychromatic418967fa.accept_19_8_1_16_1_13429 65 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 225 3 21 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 62
  96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 225
  (Polychromatic418967fa.accept_10_1_6_5_1_304 61 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 225 3 20 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 225 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 96 225 3 19 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 96 225
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 56 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 225 3 18 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 53
  96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 52 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 96 225 3 17 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 96 225 (Polychromatic418967fa.accept_18_14_6_9_1_1950 50 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 225 (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 225 3 16 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 225
  (Polychromatic418967fa.accept_11_3_8_5_1_336 47 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 225 3 15 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 44
  96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 225
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 43 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 225 3 14 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 225 (Polychromatic418967fa.accept_13_1_5_4_1_463 40 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 225 3 13 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 225 (Polychromatic418967fa.accept_18_1_6_9_1_2001 37 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 225 3 12 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219
  35 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 34 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 96 225 3 11 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 96 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 225 3 10 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 225
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 225 (Polychromatic418967fa.accept_13_2_5_4_1_3926 28 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 225 3 9 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 225 (Polychromatic418967fa.accept_18_8_6_9_1_5576 26 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 225 3 8 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 225 (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 225 (Polychromatic418967fa.accept_13_9_5_4_1_1591 22 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 225 3 7 32 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 225 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 225 3 6 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 225
  (Polychromatic418967fa.accept_26_16_18_17_1_13428 16 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 96 225 3 5 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 96 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 96 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 13
  96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 225 3 4 32 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 225 3 3 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 225 (Polychromatic418967fa.accept_18_8_6_9_1_5576 8 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 225
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 7 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 225 3 2 32 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 225 (Polychromatic418967fa.accept_19_5_1_16_1_6501 5 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 96 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 225 3 1 32 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 225
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 96 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 96 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 225
  (allA_succ_of_accept 94 95 225 (accept_3_4 94 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 225 (Polychromatic418967fa.accept_20_13_15_5_1_4628 93 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 225 (accept_3_4 91 95 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 90 95 225 5 18 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 95 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 95 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 95 225 (accept_3_4 88 95 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 95 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 87
  95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 95 225 5 17 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 95 225 (Polychromatic418967fa.accept_18_12_5_9_1_6896 84 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 225 (Polychromatic418967fa.accept_17_15_10_4_1_8540 83 95
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 225 (accept_3_4 82 95 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 225 (Polychromatic418967fa.accept_20_1_15_5_1_9135
  81 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 95 225 5 16 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 95 225 (accept_3_4 79
  95 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 95 225 (Polychromatic418967fa.accept_20_17_15_5_1_4627 77 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 225 (accept_3_4 76 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 95 225 5 15 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 95 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 225 (accept_3_4 73 95 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 225 (Polychromatic418967fa.accept_16_8_15_1_1_3006 72 95
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 225
  (Polychromatic418967fa.accept_20_11_15_5_1_10632 71 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 95 225 5 14 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 95 225 (Polychromatic418967fa.accept_16_5_15_1_1_2113 69 95 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 225
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 95 225 (accept_3_4 67 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  95 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 95 225 5 13 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 95 225 (accept_3_4 64 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 95 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 95 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 225 (accept_3_4 61 95 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 95 225 5 12 19 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 95 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 225 (accept_3_4 58 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 225 (Polychromatic418967fa.accept_17_6_10_4_1_6007 57 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 95 225 5 11 19 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 95 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 95 225 (Polychromatic418967fa.accept_11_9_7_5_1_749 53 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 225 (accept_3_4 52 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 95 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 95 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 225 5 10 19 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 225 (accept_3_4 49 95 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 225 (Polychromatic418967fa.accept_18_12_5_9_1_6896 48 95
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 225 (accept_3_4 46 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 95
  225 5 9 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  95 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 95 225 (accept_3_4 43 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 95 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 225 (Polychromatic418967fa.accept_20_1_15_5_1_9135 41 95
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 95 225 5 8 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 95 225
  (Polychromatic418967fa.accept_12_3_11_9_1_193 39 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 95 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 225 (accept_3_4 37 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 95 225 (Polychromatic418967fa.accept_20_16_15_5_1_7740 36 95 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 225 5 7 19 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 225 (accept_3_4 34 95 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 95 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 225
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 225 (accept_3_4 31 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 95
  225 5 6 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  95 225 (Polychromatic418967fa.accept_20_9_15_5_1_4670 29 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 95 225 (accept_3_4 28 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 95 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 95 225 5 5 19 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 95 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 95 225 (Polychromatic418967fa.accept_17_6_10_4_1_6007 23 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 225 (accept_3_4 22 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 95 225 (Polychromatic418967fa.accept_16_5_15_1_1_2113 21 95 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 225 5 4 19 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 225 (accept_3_4 19 95 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 225 (accept_3_4 16 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 95
  225 5 3 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  95 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 95 225 (accept_3_4 13 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 95 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 225 (Polychromatic418967fa.accept_16_11_15_1_1_2074 11 95
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 95 225 5 2 19 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 95 225
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 225 (accept_3_4 7 95 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 225 5 1 19 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 225 (accept_3_4 4 95 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 95 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 225 (accept_3_4 1 95 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 225
  (allA_succ_of_accept 93 94 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 225 (accept_3_5 92 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 225 (Polychromatic418967fa.accept_12_6_10_9_1_531
  90 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 225 (accept_3_5 89
  94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 88 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 225 (accept_3_5 86 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 225 (Polychromatic418967fa.accept_16_4_14_1_1_1241
  84 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 225 (accept_3_5 83
  94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 82 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 94 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 94 225 (accept_3_5 80 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 94 225 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  78 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 225 (accept_3_5 77
  94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 225
  (Polychromatic418967fa.accept_10_6_4_5_1_615 76 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 225 (accept_3_5 74 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 94 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 72
  94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 225 (accept_3_5 71 94
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 225
  (Polychromatic418967fa.accept_17_2_9_4_1_3463 70 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 94 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 69 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 225 (accept_3_5 68 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 225 (Polychromatic418967fa.accept_10_6_4_5_1_615
  66 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 225 (accept_3_5 65
  94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 225
  (Polychromatic418967fa.accept_13_12_3_4_1_928 64 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 225 (accept_3_5 62 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 94 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 60
  94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 225 (accept_3_5 59 94
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 225 (Polychromatic418967fa.accept_7_2_3_1_1_10
  58 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 225
  (Polychromatic418967fa.accept_30_27_4_15_1_13427 57 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 94 225 (accept_3_5 56 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 94 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 225 (accept_3_5 53 94 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 225 (Polychromatic418967fa.accept_16_4_14_1_1_1241
  52 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 225 (accept_3_5 50 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 225 (Polychromatic418967fa.accept_17_14_9_4_1_3465 48 94 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 225 (accept_3_5 47 94 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 94 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 225
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 225 (accept_3_5 44 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 225 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 225 (accept_3_5 41 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 94 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 225 (accept_3_5 38 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 225 (accept_3_5 35 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 225 (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 94 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 225 (accept_3_5 32 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 225 (accept_3_5 29 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 225 (Polychromatic418967fa.accept_19_9_18_16_1_7938 28 94 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 225 (accept_3_5 26 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 225 (Polychromatic418967fa.accept_21_3_10_15_1_4266 24 94 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 225 (accept_3_5 23 94 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 225 (Polychromatic418967fa.accept_19_3_18_16_1_6483 22 94
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 225
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 225 (accept_3_5 20 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 225 (accept_3_5 17 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 94 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 225 (accept_3_5 14 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 225 (accept_3_5 11 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 225 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 94 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 225 (accept_3_5 8 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 225 (accept_3_5 5 94 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 94 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 225 (accept_3_5 2 94 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 225
  (allA_succ_of_accept 92 93 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 92 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 225 (Polychromatic418967fa.accept_18_1_3_9_1_328 91 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 225 3 30 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 225
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 89 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 225 (Polychromatic418967fa.accept_10_8_3_5_1_613 88 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 225 3 29 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 225 (Polychromatic418967fa.accept_17_1_8_4_1_1519
  86 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 225
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 85 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 225 3 28 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 225 (Polychromatic418967fa.accept_10_2_3_5_1_996 82 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 225 3 27 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 225 (Polychromatic418967fa.accept_18_7_3_9_1_1020 79 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 225 3 26 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 77
  93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 76 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 225 3 25 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 225 (Polychromatic418967fa.accept_18_2_3_9_1_1996 74 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 225 3 24 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 225
  (Polychromatic418967fa.accept_13_6_2_4_1_923 71 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 225 (Polychromatic418967fa.accept_13_5_2_4_1_3955 70 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 225 3 23 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 68
  93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 225
  (Polychromatic418967fa.accept_10_7_3_5_1_301 67 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 225 3 22 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 225 (Polychromatic418967fa.accept_19_8_17_16_1_6497 65 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 225 (Polychromatic418967fa.accept_13_12_2_4_1_3131 64 93
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 225 3 21 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 225 (Polychromatic418967fa.accept_18_7_3_9_1_1020 61 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 225 3 20 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 59
  93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 225
  (Polychromatic418967fa.accept_10_8_3_5_1_613 58 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 225 3 19 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 225 (Polychromatic418967fa.accept_18_2_3_9_1_1996 56 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 225 3 18 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 225
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 53 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 225 3 17 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 225 (Polychromatic418967fa.accept_13_11_2_4_1_1590
  50 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 225
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 49 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 225 3 16 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 225 (Polychromatic418967fa.accept_16_14_13_1_1_5278 46 93
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 225 3 15 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 225
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 225 (Polychromatic418967fa.accept_18_7_3_9_1_1020 43 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 225 3 14 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 41
  93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 225
  (Polychromatic418967fa.accept_19_2_17_16_1_6481 40 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 225 3 13 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 225 3 12 31 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 225
  (Polychromatic418967fa.accept_16_3_13_1_1_1206 35 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 225 3 11 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 225 (Polychromatic418967fa.accept_10_2_3_5_1_996 32
  93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 225 3 10 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 225 (Polychromatic418967fa.accept_17_12_8_4_1_2518 29 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 225 3 9 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 225
  (Polychromatic418967fa.accept_18_8_3_9_1_4232 26 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 225 (Polychromatic418967fa.accept_13_12_2_4_1_3131 25 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 225 3 8 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 225 (Polychromatic418967fa.accept_21_2_9_15_1_5747 23 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 225
  (Polychromatic418967fa.accept_10_2_3_5_1_996 22 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 225 3 7 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 225 (Polychromatic418967fa.accept_13_6_2_4_1_923 19 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 225 3 6 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 225 (Polychromatic418967fa.accept_21_16_9_15_1_4265 16 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 225 3 5 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 225 (Polychromatic418967fa.accept_16_14_13_1_1_5278 14 93
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 225 3 4 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 225 (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 225 3 3 31 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 225
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 225 3 2 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 225 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 225
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 93 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 225 3 1 31 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 225 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 93 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 225 (Polychromatic418967fa.accept_17_1_8_4_1_1519 1 93 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 225
  (allA_succ_of_accept 91 92 225 (accept_3_4 91 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 90 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 225 (accept_3_4 88 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 87 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 225
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 86 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 225 (accept_3_4 85 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 225 (Polychromatic418967fa.accept_16_4_12_1_1_1204 84 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 225 (accept_3_4 82 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 225 (Polychromatic418967fa.accept_13_3_1_4_1_945 81 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 225
  (Polychromatic418967fa.accept_17_12_7_4_1_7231 80 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 225 (accept_3_4 79 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 78 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 225 (accept_3_4 76 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 225 (Polychromatic418967fa.accept_13_10_1_4_1_3103 75 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 225
  (Polychromatic418967fa.accept_27_20_11_9_1_11593 74 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 92 225 (accept_3_4 73 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 92 225 (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 92 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 225 (accept_3_4 70 92 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 69
  92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 68 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 225 (accept_3_4 67 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 225 (accept_3_4 64 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 225 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 225
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 62 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 225 (accept_3_4 61 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 225 (Polychromatic418967fa.accept_18_6_2_9_1_3056 60 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 225 (accept_3_4 58 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 225
  (Polychromatic418967fa.accept_16_8_12_1_1_7720 56 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 225 (accept_3_4 55 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 225 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 225 (accept_3_4 52 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 225 (Polychromatic418967fa.accept_14_9_8_1_1_2381 51 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 225
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 50 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 225 (accept_3_4 49 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 225 (accept_3_4 46 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 225
  (Polychromatic418967fa.accept_13_5_1_4_1_3966 44 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 225 (accept_3_4 43 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 225 (accept_3_4 40 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 225 (Polychromatic418967fa.accept_18_3_2_9_1_1013 39 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 225 (accept_3_4 37 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 225 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 225 (accept_3_4 34 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 225 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 225
  (Polychromatic418967fa.accept_11_10_4_5_1_359 32 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 225 (accept_3_4 31 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 225 (accept_3_4 28 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 225
  (Polychromatic418967fa.accept_20_6_12_5_1_9151 26 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 225 (accept_3_4 25 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 225 (Polychromatic418967fa.accept_16_8_12_1_1_7720 24 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 225 (accept_3_4 22 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 225
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 20 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 225 (accept_3_4 19 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 225 (accept_3_4 16 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 225 (Polychromatic418967fa.accept_20_15_12_5_1_11958 15 92 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 225
  (Polychromatic418967fa.accept_17_14_7_4_1_3476 14 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 225 (accept_3_4 13 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 225 (Polychromatic418967fa.accept_17_12_7_4_1_7231 12 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 225 (accept_3_4 10 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 225 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 92 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 225 (accept_3_4 7 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  225 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 225 (accept_3_4 4 92 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 225 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 92 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 225 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2
  92 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 225 (accept_3_4 1 92 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 225
  (allA_succ_of_accept 90 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 225 (accept_3_5 89 91 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  87 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 225 (accept_3_5 86
  91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 225
  (Polychromatic418967fa.accept_11_8_3_5_1_355 85 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 84 91 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 225 (accept_3_5 83 91 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 225
  (Polychromatic418967fa.accept_21_18_7_15_1_2877 81 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 91 225 (accept_3_5 80 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  91 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 79 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 225 (accept_3_5 77 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 225
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 75 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 225 (accept_3_5 74 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 225 (Polychromatic418967fa.accept_17_5_6_4_1_8607 73 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 225 (Polychromatic418967fa.accept_21_9_7_15_1_5769 72 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 225 (accept_3_5 71 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 225
  (Polychromatic418967fa.accept_10_9_1_5_1_594 69 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 225 (accept_3_5 68 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 225 (Polychromatic418967fa.accept_22_1_3_5_1_375 67 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 225 (accept_3_5 65 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 225
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 225 (accept_3_5 62 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 225 (Polychromatic418967fa.accept_17_10_6_4_1_2506 61 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 225 (Polychromatic418967fa.accept_16_12_11_1_1_4088 60 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 225 (accept_3_5 59 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 225
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 57 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 225 (accept_3_5 56 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 225 (Polychromatic418967fa.accept_14_13_7_1_1_1618 55 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 225 (accept_3_5 53 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 225
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 225 (accept_3_5 50 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 225 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 225 (accept_3_5 47 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 225
  (Polychromatic418967fa.accept_17_11_6_4_1_4729 45 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 225 (accept_3_5 44 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 225 (Polychromatic418967fa.accept_21_1_7_15_1_4259 43 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 225 (accept_3_5 41 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 225
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 225 (accept_3_5 38 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 225 (Polychromatic418967fa.accept_19_18_15_16_1_6528 37 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 225 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 225 (accept_3_5 35 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 225
  (Polychromatic418967fa.accept_21_12_7_15_1_7272 33 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 225 (accept_3_5 32 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 225 (Polychromatic418967fa.accept_16_15_11_1_1_7767 31 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 225 (accept_3_5 29 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 225
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 225 (accept_3_5 26 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 225 (Polychromatic418967fa.accept_19_6_15_16_1_7972 25 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 225 (accept_3_5 23 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 225
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 21 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 225 (accept_3_5 20 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 225 (accept_3_5 17 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 225
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 225 (accept_3_5 14 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 225 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 225 (Polychromatic418967fa.accept_16_12_11_1_1_4088 12 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 225 (accept_3_5 11 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 225
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 225 (accept_3_5 8 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  225 (Polychromatic418967fa.accept_27_7_10_9_1_9669 7 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 225 (accept_3_5 5 91 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 225
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 225 (accept_3_5 2 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  225 (Polychromatic418967fa.accept_19_1_15_16_1_2553 1 91 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 225
  (allA_succ_of_accept 89 90 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 88 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 225 3 29 30 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 86 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 90 225 5 17 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 90 225 3 28 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 82 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 90 225 9 9 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 90 225 5 16 18 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 225 3 26 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 90 225 (Polychromatic418967fa.accept_14_7_6_1_1_1656 77 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 225 15 5 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 225
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 74 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 90 225 (Polychromatic418967fa.accept_13_8_12_4_1_4858 73 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 225 9 8 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 225 5 14 18 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 90 225 3 23 30 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 225 3 22 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 90 225 5 13 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 90 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 64
  90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 90 225 9 7 10 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 90 225
  (Polychromatic418967fa.accept_12_2_6_9_1_19 62 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 90 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 225 15 4 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 58 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 90 225 3 19 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 90 225 (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 90 225 5 11 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 225 9 6 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 225 (Polychromatic418967fa.accept_20_13_10_5_1_3338
  53 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 225
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 90 225 3 17 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 90 225 5 10 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 225 (Polychromatic418967fa.accept_14_7_6_1_1_1656 49 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 225 3 16 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 225
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 225 45 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 225 3 14 30 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 225
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 225 5 8 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 90 225 3 13 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 90 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 225 9 4 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 225 5 7 18 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 90 225
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 90 225 3 11 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 90 225 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 225 15 2 6 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 225
  (Polychromatic418967fa.accept_13_3_12_4_1_110 29 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 90 225 9 3 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 90 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 90 225 5 5 18 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 225 3 8 30 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 225 3 7 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 225 5 4 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 225 9 2 10 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 225
  (Polychromatic418967fa.accept_19_17_14_16_1_3820 17 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 90 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 90 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 225 15 1 6 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 225
  (Polychromatic418967fa.accept_19_13_14_16_1_6527 13 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 90 225 3 4 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 90 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 225 5 2 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 225 9 1 10 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 90 225 (Polychromatic418967fa.accept_11_8_2_5_1_1769 8
  90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 225 3 2 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 90 225 5 1 18 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 90 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 90 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 225 3 1 30 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 90 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 225
  (Polychromatic418967fa.accept_17_1_5_4_1_8532 1 90 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 225 (allA_succ_of_accept 88 89 225 (accept_3_4 88 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 89 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 89 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 225 (accept_3_4 85 89 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 84
  89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 83 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 225 (accept_3_4 82 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 225 (accept_3_4 79 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 225 (Polychromatic418967fa.accept_19_2_13_16_1_5089 78 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 225
  (Polychromatic418967fa.accept_13_12_11_4_1_3111 77 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 225 (accept_3_4 76 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 225 (accept_3_4 73 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 225 (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 71 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 225 (accept_3_4 70 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 225 (accept_3_4 67 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 225
  (Polychromatic418967fa.accept_22_21_1_5_1_13426 65 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 225 (accept_3_4 64 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 225 (accept_3_4 61 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 225 (accept_3_4 58 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 225 (Polychromatic418967fa.accept_27_3_8_9_1_13425 57 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 225 (accept_3_4 55 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 225 (accept_3_4 52 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 225 (accept_3_4 49 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 225
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 47 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 225 (accept_3_4 46 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 225 (accept_3_4 43 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 225 (Polychromatic418967fa.accept_16_10_9_1_1_9973 42 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 225 (accept_3_4 40 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 225 (accept_3_4 37 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 225 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 225
  (Polychromatic418967fa.accept_20_15_9_5_1_4684 35 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 225 (accept_3_4 34 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 225 (Polychromatic418967fa.accept_13_7_11_4_1_2247 33 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 225 (accept_3_4 31 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 225 (Polychromatic418967fa.accept_18_12_17_9_1_5513 30 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 225
  (Polychromatic418967fa.accept_16_13_9_1_1_3022 29 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 225 (accept_3_4 28 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 225 (accept_3_4 25 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 225
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 225 (accept_3_4 22 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 225 (accept_3_4 19 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 225 (accept_3_4 16 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 225 (accept_3_4 13 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 225 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 225 (accept_3_4 10 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 225 (Polychromatic418967fa.accept_21_9_5_15_1_5741 9 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 225 (accept_3_4 7 89 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 89 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 225
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 5 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 225 (accept_3_4 4 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  225 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 89 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 225 (accept_3_4 1 89 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 225 (allA_succ_of_accept 87 88 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 225 (accept_3_5 86 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 225
  (Polychromatic418967fa.accept_13_6_10_4_1_957 84 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 88 225 (accept_3_5 83 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  88 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 82 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 88 225 (Polychromatic418967fa.accept_14_11_4_1_1_4255 81 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 225 (accept_3_5 80 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 225
  (Polychromatic418967fa.accept_12_6_4_9_1_544 78 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 225 (accept_3_5 77 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 225 (Polychromatic418967fa.accept_13_11_10_4_1_1565 76 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 225 (accept_3_5 74 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 72 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 225 (accept_3_5 71 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 225 (Polychromatic418967fa.accept_13_5_10_4_1_1564 70 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 225 (Polychromatic418967fa.accept_18_15_16_9_1_4299 69 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 225 (accept_3_5 68 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 225 (accept_3_5 65 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 225 (Polychromatic418967fa.accept_17_13_3_4_1_2537 64 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 225 (accept_3_5 62 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 225
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 60 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 225 (accept_3_5 59 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 225 (Polychromatic418967fa.accept_13_6_10_4_1_957 58 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 225 (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 225 (accept_3_5 56 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 225 (accept_3_5 53 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 225 (Polychromatic418967fa.accept_18_15_16_9_1_4299 51 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 225 (accept_3_5 50 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 225
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 48 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 225 (accept_3_5 47 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 225 (Polychromatic418967fa.accept_13_7_10_4_1_919 46 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 225 (accept_3_5 44 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 225 (accept_3_5 41 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 225 (Polychromatic418967fa.accept_14_11_4_1_1_4255 39 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 225 (accept_3_5 38 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 225
  (Polychromatic418967fa.accept_16_4_8_1_1_5257 36 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 225 (accept_3_5 35 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 225 (Polychromatic418967fa.accept_13_8_10_4_1_2270 34 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 225 (accept_3_5 32 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 225
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 225 (accept_3_5 29 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 225 (Polychromatic418967fa.accept_16_12_8_1_1_5270 28 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 225 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 225 (accept_3_5 26 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 225 (accept_3_5 23 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 225 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 225 (accept_3_5 20 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 225
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 225 (accept_3_5 17 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 225 (Polychromatic418967fa.accept_17_16_3_4_1_6010 16 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 225 (Polychromatic418967fa.accept_16_15_8_1_1_9959 15 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 225 (accept_3_5 14 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 225 (accept_3_5 11 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 225 (Polychromatic418967fa.accept_16_9_8_1_1_1228 9 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 225 (accept_3_5 8 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 225
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 225 (accept_3_5 5 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  225 (Polychromatic418967fa.accept_16_4_8_1_1_5257 4 88 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 225 (accept_3_5 2 88 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 225
  (allA_succ_of_accept 86 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 85 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 225 3 28 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 225
  (Polychromatic418967fa.accept_10_3_7_5_1_288 83 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 225 3 27 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 225 (Polychromatic418967fa.accept_17_12_2_4_1_11050
  80 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 79 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 225 3 26 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 225 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 225 (Polychromatic418967fa.accept_18_4_15_9_1_6882 76 87
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 225 3 25 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 225 3 24 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  71 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 225 3 23 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 225 3 22 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 225 (Polychromatic418967fa.accept_18_10_15_9_1_1054 64 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 225 3 21 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 225 3 20 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 225 (Polychromatic418967fa.accept_11_4_10_5_1_1202 59 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 225 3 19 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 225
  (Polychromatic418967fa.accept_16_8_7_1_1_8875 56 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 225 3 18 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 225
  (Polychromatic418967fa.accept_10_2_7_5_1_605 52 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 225 3 17 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 225 3 16 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 225 3 15 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 44
  87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 225
  (Polychromatic418967fa.accept_10_3_7_5_1_288 43 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 225 3 14 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 225 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 225 3 13 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 225 3 12 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 225 3 11 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 225 3 10 29 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 225
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 225 3 9 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 225 3 8 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 225 3 7 29 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 225
  (Polychromatic418967fa.accept_13_7_9_4_1_918 20 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 225 3 6 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 225 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 225 3 5 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 225 3 4 29 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 225 3 3 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 225
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 225 3 2 29 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 87 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 225 3 1 29 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 87 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 225
  (allA_succ_of_accept 85 86 225 (accept_3_4 85 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 84 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 225 (accept_3_4 82 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 81 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 225 (accept_3_4 79 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 225 (accept_3_4 76 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 225
  (Polychromatic418967fa.accept_10_4_6_5_1_74 74 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 225 (accept_3_4 73 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 225 (Polychromatic418967fa.accept_20_12_6_5_1_7734 72 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 225 (accept_3_4 70 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 225
  (Polychromatic418967fa.accept_23_22_17_18_1_13424 68 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 86 225 (accept_3_4 67 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 86 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 86 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 86 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 86 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 225 (accept_3_4 64 86 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 63
  86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 225 (accept_3_4 61 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 225 (Polychromatic418967fa.accept_18_6_14_9_1_3039 60 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 225 (accept_3_4 58 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 225 (Polychromatic418967fa.accept_18_3_14_9_1_4264 57 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 225
  (Polychromatic418967fa.accept_17_5_1_4_1_3460 56 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 225 (accept_3_4 55 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 225 (accept_3_4 52 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 225
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 50 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 225 (accept_3_4 49 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 225 (accept_3_4 46 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 225
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 225 (accept_3_4 43 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 225 (accept_3_4 40 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 225 (accept_3_4 37 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 225 (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 225 (accept_3_4 34 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 225 (Polychromatic418967fa.accept_22_11_20_5_1_13423 33 86 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 225
  (Polychromatic418967fa.accept_19_13_10_16_1_9334 32 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 86 225 (accept_3_4 31 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 86 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 86 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 86 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 225 (accept_3_4 28 86 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 225
  (Polychromatic418967fa.accept_19_7_10_16_1_9388 26 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 225 (accept_3_4 25 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 225 (accept_3_4 22 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 225 (accept_3_4 19 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 225 (accept_3_4 16 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 225
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 225 (accept_3_4 13 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 225 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 225 (accept_3_4 10 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 225 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 86 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 225
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 225 (accept_3_4 7 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  225 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 225 (accept_3_4 4 86 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 225 (Polychromatic418967fa.accept_16_2_6_1_1_2069 2
  86 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 225 (accept_3_4 1 86 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 225
  (allA_succ_of_accept 84 85 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 225 (accept_3_5 83 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 85 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 225 (Polychromatic418967fa.accept_13_3_7_4_1_435
  81 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 85 225 5 16 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 85 225
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 79 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 225 (Polychromatic418967fa.accept_18_6_13_9_1_4218 78 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 225 (accept_3_5 77 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 85 225 5 15 17 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 85 225 (accept_3_5 74 85 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 225 (Polychromatic418967fa.accept_16_9_5_1_1_1259 73 85 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 225
  (Polychromatic418967fa.accept_27_18_4_9_1_13422 72 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 225 (accept_3_5 71 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 85
  225 5 14 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  85 225 (Polychromatic418967fa.accept_11_3_8_5_1_336 69 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 85 225 (accept_3_5 68 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 85 225 (Polychromatic418967fa.accept_19_10_9_16_1_5085 67 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 225 (Polychromatic418967fa.accept_21_3_1_15_1_4287 66 85
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 85 225 5 13 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 85 225
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 85 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 225 (accept_3_5 62 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 225 (Polychromatic418967fa.accept_13_9_7_4_1_953 61 85 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 225 5 12 17 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 225 (accept_3_5 59 85 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 85 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 225
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 225 (accept_3_5 56 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 85
  225 5 11 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  85 225 (Polychromatic418967fa.accept_16_6_5_1_1_7761 54 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 85 225 (accept_3_5 53 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 85 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 85 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 85 225 5 10 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 85 225
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 49 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 225 (Polychromatic418967fa.accept_13_9_7_4_1_953 48 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 225 (accept_3_5 47 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 85 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 225 5 9 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 225 (accept_3_5 44 85 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 225 (Polychromatic418967fa.accept_29_14_27_22_1_13421 43 85 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 225
  (Polychromatic418967fa.accept_13_3_7_4_1_435 42 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 225 (accept_3_5 41 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 85
  225 5 8 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  85 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 85 225 (accept_3_5 38 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 85 225 (Polychromatic418967fa.accept_13_11_7_4_1_1561 37 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 85 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 85 225 5 7 17 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 85 225
  (Polychromatic418967fa.accept_6_4_1_3_1_77 34 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 225 (Polychromatic418967fa.accept_19_14_9_16_1_7969 33 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 225 (accept_3_5 32 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 225 (Polychromatic418967fa.accept_16_15_5_1_1_7724 31 85 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 225 5 6 17 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 225 (accept_3_5 29 85 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 225
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 225 (accept_3_5 26 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85
  225 5 5 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  85 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 85 225 (accept_3_5 23 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 85 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 225 (Polychromatic418967fa.accept_18_3_13_9_1_4260 21 85
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 225 5 4 17 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 225
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 225 (Polychromatic418967fa.accept_19_18_9_16_1_6524 18 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 225 (accept_3_5 17 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 225 5 3 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 225 (accept_3_5 14 85 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 85 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 225
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 225 (accept_3_5 11 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  225 5 2 17 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 225 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 225 (accept_3_5 8 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 225 (Polychromatic418967fa.accept_19_7_9_16_1_10774 7 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 225 (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 85 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 225 5 1 17 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 225
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 225 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 225 (accept_3_5 2 85 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 225 (Polychromatic418967fa.accept_24_1_13_9_1_13420 1 85 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 225
  (allA_succ_of_accept 83 84 225 (Polychromatic418967fa.accept_13_5_6_4_1_1582 83 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 225 (Polychromatic418967fa.accept_18_10_12_9_1_2012 82 84
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 225 3 27 28 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 225
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 80 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 79 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 225 3 26 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 77
  84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 84 225
  (Polychromatic418967fa.accept_10_6_4_5_1_615 76 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 84 225 3 25 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 84 225 (Polychromatic418967fa.accept_13_9_6_4_1_2243 74 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 225 (Polychromatic418967fa.accept_17_5_16_4_1_4734 73 84
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 225 3 24 28 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 225
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 71 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 225 (Polychromatic418967fa.accept_13_5_6_4_1_1582 70 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 225 3 23 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 225 (Polychromatic418967fa.accept_19_11_8_16_1_7988
  68 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 225
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 67 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 225 3 22 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 225 (Polychromatic418967fa.accept_18_11_12_9_1_992 65 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 225 (Polychromatic418967fa.accept_11_9_7_5_1_749 64 84 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 225 3 21 28 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 225
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 62 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 84 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 225 3 20 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 59
  84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 225
  (Polychromatic418967fa.accept_18_4_12_9_1_2011 58 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 84 225 3 19 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 84 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 56 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 225 (Polychromatic418967fa.accept_19_17_8_16_1_12029 55 84
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 225 3 18 28 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 225
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 225 (Polychromatic418967fa.accept_18_16_12_9_1_5504 52 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 225 3 17 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 225 (Polychromatic418967fa.accept_13_11_6_4_1_3121
  50 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 225
  (Polychromatic418967fa.accept_10_9_4_5_1_616 49 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 225 3 16 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 225 (Polychromatic418967fa.accept_18_11_12_9_1_992 47 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 84 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 225 3 15 28 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 225
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 44 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 225 (Polychromatic418967fa.accept_19_5_8_16_1_10789 43 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 225 3 14 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 225 (Polychromatic418967fa.accept_10_1_4_5_1_1031
  41 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 225
  (Polychromatic418967fa.accept_16_8_4_1_1_2102 40 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 84 225 3 13 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 84 225 (Polychromatic418967fa.accept_22_16_18_5_1_8731 38 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 84 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 225 3 12 28 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 225
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 225 (Polychromatic418967fa.accept_18_16_12_9_1_5504 34 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 225 3 11 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 225 (Polychromatic418967fa.accept_17_15_16_4_1_2418
  32 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 225
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 225 3 10 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 225 (Polychromatic418967fa.accept_13_2_6_4_1_1593 28 84 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 225 3 9 28 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 225
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 225 (Polychromatic418967fa.accept_19_6_8_16_1_13419 25 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 225 3 8 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 225 (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 84 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 225
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 22 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 225 3 7 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 225 (Polychromatic418967fa.accept_11_9_7_5_1_749 20 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 84 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 225 3 6 28 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 225
  (Polychromatic418967fa.accept_18_17_12_9_1_3031 17 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 225 3 5 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 225 (Polychromatic418967fa.accept_16_14_4_1_1_3049 14 84 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 225
  (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 225 3 4 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 225 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 225 (Polychromatic418967fa.accept_13_10_6_4_1_1583 10 84
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 225 3 3 28 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 225
  (Polychromatic418967fa.accept_16_8_4_1_1_2102 8 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 225 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 225 3 2 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 225
  (Polychromatic418967fa.accept_18_4_12_9_1_2011 4 84 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 84 225 3 1 28 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 84 225 (Polychromatic418967fa.accept_13_2_6_4_1_1593 2 84 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 225 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 84 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 225
  (allA_succ_of_accept 82 83 225 (accept_3_4 82 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 225 (Polychromatic418967fa.accept_20_1_3_5_1_1060 81 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 225 (accept_3_4 79 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 225
  (Polychromatic418967fa.accept_10_7_3_5_1_301 77 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 225 (accept_3_4 76 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 225 (accept_3_4 73 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 225
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 71 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 225 (accept_3_4 70 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 225 (Polychromatic418967fa.accept_18_15_11_9_1_4256 69 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 225 (accept_3_4 67 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 225 (accept_3_4 64 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 225 (accept_3_4 61 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 225 (Polychromatic418967fa.accept_21_18_20_15_1_8916 60 83 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 225
  (Polychromatic418967fa.accept_19_2_7_16_1_9312 59 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 225 (accept_3_4 58 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 225 (accept_3_4 55 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 225
  (Polychromatic418967fa.accept_13_1_5_4_1_463 53 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 225 (accept_3_4 52 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 225 (accept_3_4 49 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 225 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 225 (accept_3_4 46 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 225 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 225 (accept_3_4 43 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 225
  (Polychromatic418967fa.accept_13_2_5_4_1_3926 41 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 225 (accept_3_4 40 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 225 (accept_3_4 37 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 225 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 225
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 225 (accept_3_4 34 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 225 (accept_3_4 31 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 225
  (Polychromatic418967fa.accept_16_13_3_1_1_2100 29 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 225 (accept_3_4 28 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 225 (accept_3_4 25 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 225 (Polychromatic418967fa.accept_30_24_23_15_1_6886 24 83 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 225 (accept_3_4 22 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 225 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 225 (accept_3_4 19 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 225
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 225 (accept_3_4 16 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 225 (accept_3_4 13 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 225
  (Polychromatic418967fa.accept_17_11_15_4_1_2415 11 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 225 (accept_3_4 10 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 225 (accept_3_4 7 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 225 (accept_3_4 4 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  225 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 83 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 225 (accept_3_4 1 83 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 225
  (allA_succ_of_accept 81 82 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 82 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 225 (accept_3_5 80 82 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 225 (Polychromatic418967fa.accept_10_8_2_5_1_596
  78 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 225 (accept_3_5 77
  82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 76 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 225 (accept_3_5 74 82 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 82 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 225
  (Polychromatic418967fa.accept_19_15_6_16_1_6506 72 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 225 (accept_3_5 71 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 225 (Polychromatic418967fa.accept_16_6_2_1_1_4081 70 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 225 (accept_3_5 68 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 225 (accept_3_5 65 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 225 (Polychromatic418967fa.accept_17_13_14_4_1_2468 64 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 225 (accept_3_5 62 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 225 (accept_3_5 59 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 225 (accept_3_5 56 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 225
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 225 (accept_3_5 53 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 225 (accept_3_5 50 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 225 (accept_3_5 47 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 225 (accept_3_5 44 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 225
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 225 (accept_3_5 41 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 225 (Polychromatic418967fa.accept_22_18_16_5_1_5387 40 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 225 (accept_3_5 38 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 225
  (Polychromatic418967fa.accept_22_14_16_5_1_11815 36 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 82 225 (accept_3_5 35 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 82 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 82 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 225 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 82 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 225 (accept_3_5 32 82 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 225
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 225 (accept_3_5 29 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 225 (accept_3_5 26 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 225 (accept_3_5 23 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 225 (Polychromatic418967fa.accept_16_6_2_1_1_4081 22 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 225 (Polychromatic418967fa.accept_22_21_16_5_1_13418 21 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 225 (accept_3_5 20 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 225 (accept_3_5 17 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 225 (Polychromatic418967fa.accept_23_16_13_18_1_13417 16 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 225 (accept_3_5 14 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 225
  (Polychromatic418967fa.accept_16_12_2_1_1_1215 12 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 225 (accept_3_5 11 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 225 (Polychromatic418967fa.accept_16_9_2_1_1_3077 9 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 225 (accept_3_5 8 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 225 (accept_3_5 5 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  225 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 82 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 225 (accept_3_5 2 82 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 225
  (allA_succ_of_accept 80 81 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 79 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 225 3 26 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 225
  (Polychromatic418967fa.accept_13_12_3_4_1_928 77 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 225 (Polychromatic418967fa.accept_10_6_1_5_1_1024 76 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 225 3 25 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  74 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 73 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 225 9 8 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 225 (Polychromatic418967fa.accept_17_3_13_4_1_8530 71 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 225 (Polychromatic418967fa.accept_20_10_1_5_1_7745 70 81
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 225 3 23 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 225 (Polychromatic418967fa.accept_19_10_5_16_1_6522 67 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 225 3 22 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 225 (Polychromatic418967fa.accept_11_10_4_5_1_359
  65 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 225
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 64 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 225 9 7 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 225 (Polychromatic418967fa.accept_21_20_18_15_1_11881 62 81 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 61
  81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 225 3 20 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 225 (Polychromatic418967fa.accept_19_1_5_16_1_2587 58 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 225 3 19 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 225 (Polychromatic418967fa.accept_10_6_1_5_1_1024
  56 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 225
  (Polychromatic418967fa.accept_20_15_1_5_1_6049 55 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 225 9 6 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 225 (Polychromatic418967fa.accept_13_1_3_4_1_925 53 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 225 3 17 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 225
  (Polychromatic418967fa.accept_19_12_5_16_1_13416 50 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 81 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 81 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 225 3 16 27 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 225 (Polychromatic418967fa.accept_10_6_1_5_1_1024 46 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 81 225 9 5 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 81 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 225
  (Polychromatic418967fa.accept_11_10_4_5_1_359 43 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 81 225 3 14 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 81 225 (Polychromatic418967fa.accept_19_3_5_16_1_13380 41 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 225 3 13 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 225 (Polychromatic418967fa.accept_17_3_13_4_1_8530 37 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 225 9 4 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 225 (Polychromatic418967fa.accept_20_15_1_5_1_6049 35 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 225
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 81 225 3 11 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 81 225 (Polychromatic418967fa.accept_11_10_4_5_1_359 32 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 225 3 10 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 225
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 225 (Polychromatic418967fa.accept_21_7_18_15_1_2887 28 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 225 9 3 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 225
  (Polychromatic418967fa.accept_13_12_3_4_1_928 25 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 81 225 3 8 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 81 225 (Polychromatic418967fa.accept_20_3_1_5_1_4643 23 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 225 (Polychromatic418967fa.accept_19_3_5_16_1_13380 22 81
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 225 3 7 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 225
  (Polychromatic418967fa.accept_13_7_3_4_1_459 20 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 225 9 2 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 225
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 225 3 5 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 225 (Polychromatic418967fa.accept_21_13_18_15_1_2837 13 81
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 225 3 4 27 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 225
  (Polychromatic418967fa.accept_19_11_5_16_1_1456 11 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 225 9 1 9 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 225 (Polychromatic418967fa.accept_17_8_13_4_1_6012 8 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 225
  (Polychromatic418967fa.accept_13_7_3_4_1_459 7 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 81 225 3 2 27 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 81 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 225 3 1 27 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 225
  (Polychromatic418967fa.accept_19_2_5_16_1_7986 2 81 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 225 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 81 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 225
  (allA_succ_of_accept 79 80 225 (accept_3_4 79 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 78 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 225 (accept_3_4 76 80 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 75 80 225 5 15 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 80 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 80 225 (accept_3_4 73 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 80 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 72
  80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 80 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 225 5 14 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 225 (Polychromatic418967fa.accept_19_12_4_16_1_9310 69 80 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 80 225 (accept_3_4 67 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 80 225 (Polychromatic418967fa.accept_12_6_8_9_1_553
  66 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 80 225 5 13 16 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 80 225 (accept_3_4 64
  80 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 225
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 80 225 (Polychromatic418967fa.accept_23_16_11_18_1_13393 62 80 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 80 225 (accept_3_4 61 80 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 225 5 12 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 225 (accept_3_4 58 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 225 (Polychromatic418967fa.accept_13_5_2_4_1_3955
  57 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 225
  (Polychromatic418967fa.accept_21_14_17_15_1_9017 56 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 80 225 5 11 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 80 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 80 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 80 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 80 225 (accept_3_4 52 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  80 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 80 225 5 10 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 80 225 (accept_3_4 49 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 80 225 (Polychromatic418967fa.accept_19_10_4_16_1_7996 48 80 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 80 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 225 (accept_3_4 46 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 80 225 5 9 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 80 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 44
  80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 80 225 (accept_3_4 43 80
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 80 225
  (Polychromatic418967fa.accept_12_6_8_9_1_553 42 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 80 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 225 5 8 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 225
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 38 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 225 (accept_3_4 37 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 225 (Polychromatic418967fa.accept_17_2_12_4_1_5987 36 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 80 225 5 7 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 80 225 (accept_3_4 34 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 80 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 80 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 225 (accept_3_4 31 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 225 5 6 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29
  80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 225 (accept_3_4 28 80
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 225
  (Polychromatic418967fa.accept_21_6_17_15_1_2833 27 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 80 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 80 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 80 225 5 5 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 80 225 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 80 225 (accept_3_4 22 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  80 225 (Polychromatic418967fa.accept_18_3_8_9_1_1956 21 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 80 225 5 4 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 80 225 (accept_3_4 19 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 80 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 80 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 225 (accept_3_4 16 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 80 225 5 3 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 80 225
  (Polychromatic418967fa.accept_21_14_17_15_1_9017 14 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 80 225 (accept_3_4 13 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 80 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 80 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 225 5 2 16 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 80 225 (Polychromatic418967fa.accept_11_8_3_5_1_355 8 80 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 225 (accept_3_4 7 80 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 80 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 80 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 225 5 1 16 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 225 (accept_3_4 4 80 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 225 (Polychromatic418967fa.accept_18_3_8_9_1_1956 3 80 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 225 (accept_3_4 1 80 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 225
  (allA_succ_of_accept 78 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 225 (accept_3_5 77 79 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  75 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 225 (accept_3_5 74
  79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 73 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 225 (Polychromatic418967fa.accept_16_8_15_1_1_3006 72 79 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 225 (accept_3_5 71 79 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 69
  79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 225 (accept_3_5 68 79
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 225
  (Polychromatic418967fa.accept_34_33_11_21_1_13415 67 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 225 (accept_3_5 65 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 225
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 225 (accept_3_5 62 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 61 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 225 (Polychromatic418967fa.accept_18_6_7_9_1_4250 60 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 225 (accept_3_5 59 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 225
  (Polychromatic418967fa.accept_13_5_1_4_1_3966 57 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 225 (accept_3_5 56 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 225 (accept_3_5 53 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 225 (accept_3_5 50 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 225 (Polychromatic418967fa.accept_13_10_1_4_1_3103 49 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 225 (accept_3_5 47 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 225 (accept_3_5 44 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 225 (Polychromatic418967fa.accept_16_11_15_1_1_2074 43 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 225 (accept_3_5 41 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 225
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 225 (accept_3_5 38 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 225 (Polychromatic418967fa.accept_16_5_15_1_1_2113 37 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 225 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 225 (accept_3_5 35 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 225
  (Polychromatic418967fa.accept_19_14_3_16_1_9383 33 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 225 (accept_3_5 32 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 225 (accept_3_5 29 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 225 (accept_3_5 26 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 225 (Polychromatic418967fa.accept_19_6_3_16_1_8006 25 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 225 (accept_3_5 23 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 225 (accept_3_5 20 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 225 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 225 (accept_3_5 17 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 225
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 225 (accept_3_5 14 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 225 (Polychromatic418967fa.accept_24_12_7_9_1_9975 12 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 225 (accept_3_5 11 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 225
  (Polychromatic418967fa.accept_21_9_16_15_1_9014 9 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 225 (accept_3_5 8 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  225 (Polychromatic418967fa.accept_26_7_1_17_1_13414 7 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 225 (accept_3_5 5 79 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 225 (accept_3_5 2 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  225 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 79 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 225
  (allA_succ_of_accept 77 78 225 (Polychromatic418967fa.accept_10_7_8_5_1_1008 77 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 225 3 25 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 225
  (Polychromatic418967fa.accept_12_2_6_9_1_19 74 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 73 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 225 3 24 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 225
  (Polychromatic418967fa.accept_12_10_6_9_1_549 70 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 225 3 23 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 225 (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 225 3 22 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 225
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 65 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 64 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 225 3 21 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 62
  78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 225
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 61 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 225 3 20 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 225 3 19 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 225
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 225 3 18 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 53
  78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 52 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 225 3 17 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 225 (Polychromatic418967fa.accept_11_6_1_5_1_2388 50 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 225 (Polychromatic418967fa.accept_14_7_8_1_1_1621 49 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 225 3 16 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 225 3 15 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 225 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  44 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 225 3 14 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 225 (Polychromatic418967fa.accept_19_3_2_16_1_5132 41 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 225 3 13 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 225
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 225 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 225 3 12 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 225
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 225 3 11 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 32 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 225 3 10 26 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 225
  (Polychromatic418967fa.accept_16_13_14_1_1_2094 29 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 225 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 225 3 9 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 225
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 25 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 225 3 8 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 225 3 7 26 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 225
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 225 3 6 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 225 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 225
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 225 3 5 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 225 3 4 26 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 225 3 3 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 225 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 225 3 2 26 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 225 (Polychromatic418967fa.accept_19_5_2_16_1_8013 5 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 78 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 225 3 1 26 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 78 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 225 (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 78 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 225
  (allA_succ_of_accept 76 77 225 (accept_3_4 76 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 225 (accept_3_4 73 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 225 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 225
  (Polychromatic418967fa.accept_20_11_17_5_1_13413 71 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 77 225 (accept_3_4 70 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 77 225 (Polychromatic418967fa.accept_14_13_7_1_1_1618 69 77 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 225 (accept_3_4 67 77 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 225 (Polychromatic418967fa.accept_18_12_5_9_1_6896
  66 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 225
  (Polychromatic418967fa.accept_17_14_9_4_1_3465 65 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 225 (accept_3_4 64 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 225 (accept_3_4 61 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 225
  (Polychromatic418967fa.accept_13_7_12_4_1_450 59 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 225 (accept_3_4 58 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 225 (Polychromatic418967fa.accept_13_5_12_4_1_449 57 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 225 (accept_3_4 55 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 225 (Polychromatic418967fa.accept_13_2_12_4_1_943 54 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 225
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 225 (accept_3_4 52 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 225 (accept_3_4 49 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 225
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 47 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 225 (accept_3_4 46 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 225 (Polychromatic418967fa.accept_21_3_14_15_1_10526 45 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 225 (accept_3_4 43 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 225 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 225
  (Polychromatic418967fa.accept_13_2_12_4_1_943 41 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 225 (accept_3_4 40 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 225 (accept_3_4 37 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 225
  (Polychromatic418967fa.accept_16_3_13_1_1_1206 35 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 225 (accept_3_4 34 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 225 (accept_3_4 31 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 225 (Polychromatic418967fa.accept_16_14_13_1_1_5278 30 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 225
  (Polychromatic418967fa.accept_13_3_12_4_1_110 29 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 225 (accept_3_4 28 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 225 (accept_3_4 25 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 225 (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 225
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 225 (accept_3_4 22 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 225 (Polychromatic418967fa.accept_13_8_12_4_1_4858 21 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 225 (accept_3_4 19 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 225
  (Polychromatic418967fa.accept_19_17_1_16_1_1443 17 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 225 (accept_3_4 16 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 225 (accept_3_4 13 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 225
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 225 (accept_3_4 10 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 225 (Polychromatic418967fa.accept_16_9_13_1_1_3069 9 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 225 (accept_3_4 7 77 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 225 (Polychromatic418967fa.accept_14_6_7_1_1_78 6 77 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 225
  (Polychromatic418967fa.accept_13_5_12_4_1_449 5 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 225 (accept_3_4 4 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  225 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 77 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 225 (accept_3_4 1 77 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 225 (allA_succ_of_accept 75 76 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 225 (accept_3_5 74 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 225 (accept_3_5 71 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 225 (Polychromatic418967fa.accept_11_4_10_5_1_1202 70 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 225 (accept_3_5 68 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 225
  (Polychromatic418967fa.accept_12_6_4_9_1_544 66 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 225 (accept_3_5 65 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 225 (Polychromatic418967fa.accept_14_7_6_1_1_1656 63 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 225 (accept_3_5 62 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 225
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 60 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 225 (accept_3_5 59 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 225 (Polychromatic418967fa.accept_22_13_10_5_1_10395 57 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 225 (accept_3_5 56 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 225 (accept_3_5 53 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 225 (Polychromatic418967fa.accept_16_4_12_1_1_1204 52 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 225 (accept_3_5 50 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 225
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 225 (accept_3_5 47 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 225 (Polychromatic418967fa.accept_13_7_11_4_1_2247 46 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 225 (accept_3_5 44 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 225
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 225 (accept_3_5 41 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 225 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 225 (accept_3_5 38 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 225
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 225 (accept_3_5 35 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 225 (accept_3_5 32 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 225 (accept_3_5 29 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 225 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 225 (Polychromatic418967fa.accept_16_11_12_1_1_3001 27 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 225 (accept_3_5 26 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 225
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 225 (accept_3_5 23 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 225 (Polychromatic418967fa.accept_26_22_24_17_1_13412 22 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 225 (accept_3_5 20 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 225
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 225 (accept_3_5 17 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 225 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 225 (accept_3_5 14 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 225 (accept_3_5 11 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 225 (Polychromatic418967fa.accept_13_10_11_4_1_2248 10 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 225 (accept_3_5 8 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 225
  (Polychromatic418967fa.accept_11_6_10_5_1_341 6 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 225 (accept_3_5 5 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  225 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 76 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 225 (Polychromatic418967fa.accept_30_3_16_15_1_13411 3 76 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 225 (accept_3_5 2 76 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 225 (allA_succ_of_accept
  74 75 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 75 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 225 3 24 25 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 225
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 71 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 75 225 5 14 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 75 225 3 23 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 75 225 (Polychromatic418967fa.accept_18_14_3_9_1_4234 68 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 75 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 75 225 3 22 25 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 75 225 5 13 15 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 225
  (Polychromatic418967fa.accept_20_4_15_5_1_10633 64 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 75 225 3 21 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 75 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 75 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 225 15 4 5 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 75 225 3 19 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 75 225 (Polychromatic418967fa.accept_18_2_3_9_1_1996
  56 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 225 5 11 15 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 75 225 3 18 25 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 225 3 17 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 75 225 25 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 49
  75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 225 3 16 25 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 225
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 225 15 3 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 225 (Polychromatic418967fa.accept_13_5_10_4_1_1564 44 75 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 225
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 75 225 3 14 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 225 5 8 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 75 225 3 13 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 225 3 12 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 75 225 5 7 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 225 3 11 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 32
  75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 225 15 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 225 (Polychromatic418967fa.accept_16_12_11_1_1_4088 28 75
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 225 3 9 25 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 75 225 25 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 75 225 3 8 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 225 3 7 25 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 75 225 5 4 15 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 225
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 225 3 6 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 225 (Polychromatic418967fa.accept_20_16_15_5_1_7740 16 75
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 225 15 1 5 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 225 3 4 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 75 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 225 5 2 15 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 75 225 3 3 25 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 225
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 8 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 225 3 2 25 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 75 225 5 1 15 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 75 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 225 3 1 25 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 75 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 225 (allA_succ_of_accept
  73 74 225 (accept_3_4 73 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 225
  (Polychromatic418967fa.accept_13_7_9_4_1_918 72 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 225 (accept_3_4 70 74 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 69 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 68
  74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 225 (accept_3_4 67 74
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 225 (Polychromatic418967fa.accept_7_3_4_1_1_71
  66 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 74 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 74 225 (accept_3_4 64 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  74 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 74 225 (Polychromatic418967fa.accept_17_11_6_4_1_4729 62 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 225 (accept_3_4 61 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 225 (Polychromatic418967fa.accept_13_8_9_4_1_1552 60 74 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 74 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 74 225 (accept_3_4 58 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  74 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 74 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 56 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 225 (accept_3_4 55 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 74 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 74 225 (accept_3_4 52 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  74 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 74 225 (Polychromatic418967fa.accept_20_10_14_5_1_3331 50 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 225 (accept_3_4 49 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 225 (Polychromatic418967fa.accept_20_8_14_5_1_2119 48 74
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 74 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 74 225 (accept_3_4 46 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  74 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 74 225 (Polychromatic418967fa.accept_13_5_9_4_1_441 44 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 225 (accept_3_4 43 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 74 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 74 225 (accept_3_4 40 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  74 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 74 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 225 (accept_3_4 37 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 74 225 (accept_3_4 34 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  74 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 74 225 (Polychromatic418967fa.accept_13_6_9_4_1_2288 32 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 225 (accept_3_4 31 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 74 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 74 225 (accept_3_4 28 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  74 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 74 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 225 (accept_3_4 25 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 74 225 (accept_3_4 22 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  74 225 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 74 225 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 225 (accept_3_4 19 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 74 225 (accept_3_4 16 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  74 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 74 225 (Polychromatic418967fa.accept_11_3_8_5_1_336 14 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 225 (accept_3_4 13 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 225 (accept_3_4 10 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  74 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 74 225 (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 225 (accept_3_4 7 74 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 74 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 225 (accept_3_4 4 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 74 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 225 (accept_3_4 1 74 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  225 (allA_succ_of_accept 72 73 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 73 225 (accept_3_5 71 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 225 (Polychromatic418967fa.accept_16_5_9_1_1_2070
  69 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 225 (accept_3_5 68
  73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 67 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 73 225 (Polychromatic418967fa.accept_16_2_9_1_1_6404 66 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 225 (accept_3_5 65 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 225 (Polychromatic418967fa.accept_12_3_1_9_1_202
  63 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 225 (accept_3_5 62
  73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 73 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 225 (accept_3_5 59 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 225 (Polychromatic418967fa.accept_10_7_3_5_1_301
  57 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 225 (accept_3_5 56
  73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 225
  (Polychromatic418967fa.accept_20_15_13_5_1_6061 55 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 73 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 225 (accept_3_5 53 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 51
  73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 225 (accept_3_5 50 73
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 225
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 49 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 73 225 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 225 (accept_3_5 47 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 225 (Polychromatic418967fa.accept_16_13_9_1_1_3022
  45 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 225 (accept_3_5 44
  73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 225
  (Polychromatic418967fa.accept_21_1_10_15_1_2828 43 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 73 225 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 225 (accept_3_5 41 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 39
  73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 225 (accept_3_5 38 73
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 225 (Polychromatic418967fa.accept_7_2_3_1_1_10
  37 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 225
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 225 (accept_3_5 35 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 225 (accept_3_5 32 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 225 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 73 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 225 (accept_3_5 29 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 225 (accept_3_5 26 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 225
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 24 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 225 (accept_3_5 23 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 225 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 225 (accept_3_5 20 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 73 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 225 (accept_3_5 17 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 225 (accept_3_5 14 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 225 (Polychromatic418967fa.accept_16_13_9_1_1_3022 13 73 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 225 (accept_3_5 11 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 225 (accept_3_5 8 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 73 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 225
  (Polychromatic418967fa.accept_17_6_5_4_1_7238 6 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 225 (accept_3_5 5 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 225 (accept_3_5 2 73 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 225 (Polychromatic418967fa.accept_17_1_5_4_1_8532 1 73 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 225 (allA_succ_of_accept 71
  72 225 (Polychromatic418967fa.accept_13_6_7_4_1_2264 71 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 225 (Polychromatic418967fa.accept_19_13_15_16_1_13410 70 72 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 225 3 23 24 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 68 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 67 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 225 3 22 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 225 (Polychromatic418967fa.accept_11_10_6_5_1_1239
  65 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 225
  (Polychromatic418967fa.accept_13_12_7_4_1_3124 64 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 225 9 7 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 225 (Polychromatic418967fa.accept_13_9_7_4_1_953 61 72 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 225 3 20 24 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 225 3 19 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 225 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  56 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 55 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 225 9 6 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 225 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 72 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 225 3 17 24 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 225
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 50 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 225 (Polychromatic418967fa.accept_13_10_7_4_1_2262 49 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 225 3 16 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 47
  72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 225
  (Polychromatic418967fa.accept_19_8_15_16_1_5109 46 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 225 9 5 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 225 (Polychromatic418967fa.accept_16_12_8_1_1_5270 44 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 225 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 72 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 225 3 14 24 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 225 (Polychromatic418967fa.accept_21_19_9_15_1_4217 40 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 225 3 13 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 225
  (Polychromatic418967fa.accept_10_7_2_5_1_298 37 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 225 9 4 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 225 (Polychromatic418967fa.accept_13_9_7_4_1_953 35 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 72 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 225 3 11 24 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 225
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 225 3 10 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 225 (Polychromatic418967fa.accept_13_3_7_4_1_435 29
  72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 225 9 3 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 225 (Polychromatic418967fa.accept_20_6_12_5_1_9151 26 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 225 (Polychromatic418967fa.accept_13_12_7_4_1_3124 25 72
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 225 3 8 24 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 225
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 225 (Polychromatic418967fa.accept_13_9_7_4_1_953 22 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 225 3 7 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 72 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 225
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 225 9 2 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 225 (Polychromatic418967fa.accept_13_3_7_4_1_435 16 72 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 225 3 5 24 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 225
  (Polychromatic418967fa.accept_21_14_9_15_1_13409 14 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 72 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 225 3 4 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 225 (Polychromatic418967fa.accept_13_11_7_4_1_1561
  11 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 10 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 225 9 1 8 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 225 3 2 24 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 225
  (Polychromatic418967fa.accept_21_5_9_15_1_11924 5 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 225 (Polychromatic418967fa.accept_16_4_8_1_1_5257 4 72 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 225 3 1 24 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 225 (Polychromatic418967fa.accept_21_2_9_15_1_5747 2 72 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 225
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 72 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 225
  (allA_succ_of_accept 70 71 225 (accept_3_4 70 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 225 (accept_3_4 67 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 225
  (Polychromatic418967fa.accept_21_2_8_15_1_11906 65 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 225 (accept_3_4 64 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 225 (accept_3_4 61 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 225 (Polychromatic418967fa.accept_19_3_14_16_1_10747 60 71 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 225
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 225 (accept_3_4 58 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 225 (Polychromatic418967fa.accept_13_5_6_4_1_1582 57 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 225 (accept_3_4 55 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 225
  (Polychromatic418967fa.accept_23_7_2_18_1_6787 53 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 225 (accept_3_4 52 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 225 (accept_3_4 49 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 225 (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 71 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 225
  (Polychromatic418967fa.accept_17_13_3_4_1_2537 47 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 225 (accept_3_4 46 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 225 (Polychromatic418967fa.accept_21_3_8_15_1_4301 45 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 225 (accept_3_4 43 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 225
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 41 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 225 (accept_3_4 40 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 225 (accept_3_4 37 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 225 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 71 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 225
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 225 (accept_3_4 34 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 225 (Polychromatic418967fa.accept_13_7_6_4_1_933 33 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 225 (accept_3_4 31 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 225
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 225 (accept_3_4 28 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 225 (accept_3_4 25 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 71 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 225
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 225 (accept_3_4 22 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 225 (Polychromatic418967fa.accept_19_2_14_16_1_7992 21 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 225 (accept_3_4 19 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 225
  (Polychromatic418967fa.accept_19_17_14_16_1_3820 17 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 71 225 (accept_3_4 16 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 71 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 71 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 225 (accept_3_4 13 71 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 225
  (Polychromatic418967fa.accept_18_12_17_9_1_5513 12 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 71 225 (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 71 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 225 (accept_3_4 10 71 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 71 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 225 (accept_3_4 7 71 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 225
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 225 (accept_3_4 4 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  225 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 71 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 225 (accept_3_4 1 71 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 225 (allA_succ_of_accept 69 70 225 (Polychromatic418967fa.accept_16_5_6_1_1_2118 69 70 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 225 (accept_3_5 68 70 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 70 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 225
  (Polychromatic418967fa.accept_12_6_10_9_1_531 66 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 70 225 5 13 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 70 225 (Polychromatic418967fa.accept_13_12_5_4_1_3133 64 70 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 225 (accept_3_5 62 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 70 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 61
  70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 225 5 12 14 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 225 (accept_3_5 59
  70 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 225
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 58 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 70 225 (Polychromatic418967fa.accept_17_6_2_4_1_2421 57 70 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 225 (accept_3_5 56 70 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 70 225 5 11 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 70 225 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 70 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 225 (accept_3_5 53 70 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 225 (Polychromatic418967fa.accept_19_14_13_16_1_9318 52 70
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 225 5 10 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 70 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 225 (Polychromatic418967fa.accept_13_9_5_4_1_1591 48 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 225 (accept_3_5 47 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 225
  (Polychromatic418967fa.accept_17_12_2_4_1_11050 46 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 70 225 5 9 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 70 225 (accept_3_5 44 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 225 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 70 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 225 (accept_3_5 41 70 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 225 5 8 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 70 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 225 (accept_3_5 38 70 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 225
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 70 225 5 7 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 70 225 (Polychromatic418967fa.accept_16_2_6_1_1_2069 34 70 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 225 (Polychromatic418967fa.accept_18_15_16_9_1_4299 33 70
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 225 (accept_3_5 32 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 225 5 6 14 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 225 (accept_3_5 29
  70 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 225
  (Polychromatic418967fa.accept_13_2_5_4_1_3926 28 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 70 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 225 (accept_3_5 26 70 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 70 225 5 5 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 70 225 (Polychromatic418967fa.accept_20_4_10_5_1_3305 24 70 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 225 (accept_3_5 23 70 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 225 (Polychromatic418967fa.accept_13_9_5_4_1_1591 22 70 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 225
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 225 5 4 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 225 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 225 (accept_3_5 17 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 225
  (Polychromatic418967fa.accept_20_16_10_5_1_9133 16 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 70 225 5 3 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 70 225 (accept_3_5 14 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 225 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 70 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 225 (accept_3_5 11 70 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 225 5 2 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 225 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 225 (accept_3_5 8 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 225
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 70 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 70 225 5 1 14 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 70 225 (Polychromatic418967fa.accept_20_4_10_5_1_3305 4 70 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 225 (accept_3_5 2 70 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 225 (allA_succ_of_accept 68 69
  225 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 225 (Polychromatic418967fa.accept_20_7_9_5_1_292 67 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 225 3 22 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 65
  69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 225
  (Polychromatic418967fa.accept_10_4_9_5_1_84 64 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 69 225 3 21 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 69 225 (Polychromatic418967fa.accept_19_5_12_16_1_9303 62 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 69 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 225 3 20 23 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 225
  (Polychromatic418967fa.accept_17_8_1_4_1_9831 59 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 225 3 19 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 225 (Polychromatic418967fa.accept_10_6_9_5_1_1046
  56 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 225
  (Polychromatic418967fa.accept_20_15_9_5_1_4684 55 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 69 225 3 18 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 69 225 (Polychromatic418967fa.accept_18_17_15_9_1_5542 53 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 69 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 225 3 17 23 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 225
  (Polychromatic418967fa.accept_20_10_9_5_1_3327 50 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 225 (Polychromatic418967fa.accept_14_7_13_1_1_922 49 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 225 3 16 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 47
  69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 225
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 46 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 69 225 3 15 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 69 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 225 (Polychromatic418967fa.accept_19_5_12_16_1_9303 43 69
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 225 3 14 23 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 225 3 13 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 225 (Polychromatic418967fa.accept_16_6_5_1_1_7761
  38 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 69 225 3 12 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 69 225 (Polychromatic418967fa.accept_14_7_13_1_1_922 35 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 34 69 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 225 3 11 23 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 225
  (Polychromatic418967fa.accept_19_13_12_16_1_5087 32 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 69 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 69 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 225 3 10 23 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 225
  (Polychromatic418967fa.accept_16_13_5_1_1_3017 29 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 225 3 9 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 69 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 225
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 25 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 225 3 8 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 225 (Polychromatic418967fa.accept_16_6_5_1_1_7761 22 69 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 225 3 7 23 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 225
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 225 3 6 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 225 (Polychromatic418967fa.accept_18_17_15_9_1_5542 17 69
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 225 3 5 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 225 (Polychromatic418967fa.accept_16_13_5_1_1_3017 13 69
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 225 3 4 23 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 225 (Polychromatic418967fa.accept_18_10_15_9_1_1054 10 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 225 3 3 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 225 (Polychromatic418967fa.accept_11_8_3_5_1_355 8 69 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 225
  (Polychromatic418967fa.accept_14_7_13_1_1_922 7 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 225 3 2 23 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 69 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 225 3 1 23 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 69 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 69 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 225 (allA_succ_of_accept 67 68 225 (accept_3_4 67 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 68 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 68 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 225 (accept_3_4 64 68 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 225 (Polychromatic418967fa.accept_10_3_8_5_1_606
  63 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 225 (accept_3_4 61 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 225 (accept_3_4 58 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 225 (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 68 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 225
  (Polychromatic418967fa.accept_16_8_4_1_1_2102 56 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 225 (accept_3_4 55 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 225 (accept_3_4 52 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 225 (Polychromatic418967fa.accept_13_12_3_4_1_928 51 68 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 225
  (Polychromatic418967fa.accept_20_10_8_5_1_7735 50 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 225 (accept_3_4 49 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 225 (accept_3_4 46 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 68 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 225
  (Polychromatic418967fa.accept_16_12_4_1_1_1257 44 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 225 (accept_3_4 43 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 225 (accept_3_4 40 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 68 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 225 (accept_3_4 37 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 225 (Polychromatic418967fa.accept_26_10_16_17_1_13408 36 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 225 (accept_3_4 34 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 68 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 225 (accept_3_4 31 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 225 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 225 (accept_3_4 28 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 68 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 225
  (Polychromatic418967fa.accept_22_4_2_5_1_10405 26 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 225 (accept_3_4 25 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 225 (accept_3_4 22 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 68 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 225 (accept_3_4 19 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 225 (accept_3_4 16 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 225 (Polychromatic418967fa.accept_19_15_11_16_1_6492 15 68 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 225
  (Polychromatic418967fa.accept_13_1_3_4_1_925 14 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 225 (accept_3_4 13 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 225 (accept_3_4 10 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 225 (Polychromatic418967fa.accept_21_9_5_15_1_5741 9 68 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 225
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 225 (accept_3_4 7 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  225 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 225 (accept_3_4 4 68 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 68 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  68 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 225 (accept_3_4 1 68 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 225 (allA_succ_of_accept 66 67
  225 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 225 (accept_3_5 65 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 225 (accept_3_5 62 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 225
  (Polychromatic418967fa.accept_14_4_11_1_1_940 60 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 225 (accept_3_5 59 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 225 (Polychromatic418967fa.accept_13_5_2_4_1_3955 57 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 225 (accept_3_5 56 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 225 (Polychromatic418967fa.accept_20_15_7_5_1_2115 55 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 225 (accept_3_5 53 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 225 (accept_3_5 50 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 225 (Polychromatic418967fa.accept_17_15_16_4_1_2418 49 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 225
  (Polychromatic418967fa.accept_10_8_7_5_1_602 48 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 225 (accept_3_5 47 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 225 (accept_3_5 44 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 225 (accept_3_5 41 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 225 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 225 (accept_3_5 38 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 225 (Polychromatic418967fa.accept_13_11_2_4_1_1590 37 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 225
  (Polychromatic418967fa.accept_16_4_3_1_1_8843 36 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 225 (accept_3_5 35 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 225 (accept_3_5 32 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 225 (accept_3_5 29 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 225 (accept_3_5 26 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 225 (Polychromatic418967fa.accept_13_12_2_4_1_3131 25 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 225 (accept_3_5 23 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 225 (Polychromatic418967fa.accept_18_3_13_9_1_4260 21 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 225 (accept_3_5 20 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 225 (accept_3_5 17 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 225 (accept_3_5 14 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 225 (accept_3_5 11 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 225 (Polychromatic418967fa.accept_19_9_10_16_1_6463 9 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 225 (accept_3_5 8 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 225 (Polychromatic418967fa.accept_19_7_10_16_1_9388 7 67 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 225 (accept_3_5 5 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 67 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 225 (accept_3_5 2 67 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 225 (Polychromatic418967fa.accept_19_1_10_16_1_6510 1 67 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 225 (allA_succ_of_accept 65 66
  225 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 225 3 21 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 62
  66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 225 3 20 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 66 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 225 3 19 22 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 225
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 225 3 18 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 225
  (Polychromatic418967fa.accept_12_4_6_9_1_548 52 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 225 3 17 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 225 (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 66 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 225 3 16 22 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 225 3 15 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 44
  66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 225 3 14 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 41 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 66 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 225 3 13 22 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 225
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 225 3 12 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 225
  (Polychromatic418967fa.accept_10_4_6_5_1_74 34 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 225 3 11 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 225 3 10 22 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 225
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 225 3 9 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 66 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 225 3 8 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 66 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 225 3 7 22 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 225
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 225 3 6 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 225 (Polychromatic418967fa.accept_18_17_12_9_1_3031 17 66
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 225 3 5 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 225 (Polychromatic418967fa.accept_23_13_20_18_1_13407 13 66
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 225 3 4 22 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 225 3 3 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 225 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 66 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 225 3 2 22 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 66 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 225 3 1 22 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 66 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 66 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 225 (allA_succ_of_accept 64 65 225 (accept_3_4 64 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 65 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 225 (accept_3_4 61 65 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 65 225 5 12 13 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 65 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 225 (accept_3_4 58 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 225 (Polychromatic418967fa.accept_27_3_11_9_1_13406 57 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 65 225 5 11 13 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 65 225
  (Polychromatic418967fa.accept_24_6_17_9_1_13405 54 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 65 225 (Polychromatic418967fa.accept_19_15_8_16_1_10745 53 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 225 (accept_3_4 52 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 65 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 65 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 225 5 10 13 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 225 (accept_3_4 49 65 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 65 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 225
  (Polychromatic418967fa.accept_17_13_14_4_1_2468 47 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 225 (accept_3_4 46 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 65
  225 5 9 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  65 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 65 225 (accept_3_4 43 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 65 225 (Polychromatic418967fa.accept_22_20_21_5_1_13404 42 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 65 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 65 225 5 8 13 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 65 225
  (Polychromatic418967fa.accept_11_6_10_5_1_341 39 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 65 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 225 (accept_3_4 37 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 225 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 65 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 225 5 7 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 225 (accept_3_4 34 65 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 225 (Polychromatic418967fa.accept_18_15_11_9_1_4256 33 65 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 225
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 225 (accept_3_4 31 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 65
  225 5 6 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  65 225 (Polychromatic418967fa.accept_19_10_8_16_1_9300 29 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 65 225 (accept_3_4 28 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 65 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 65 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 65 225 5 5 13 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 65 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 65 225 (Polychromatic418967fa.accept_22_1_21_5_1_10380 23 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 225 (accept_3_4 22 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 65 225 (Polychromatic418967fa.accept_27_21_11_9_1_13403 21 65 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 225 5 4 13 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 225 (accept_3_4 19 65 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 225 (Polychromatic418967fa.accept_17_1_14_4_1_1550 18 65
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 225 (accept_3_4 16 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 65
  225 5 3 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  65 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 65 225 (accept_3_4 13 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 65 225 (Polychromatic418967fa.accept_18_12_11_9_1_4257 12 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 225 (Polychromatic418967fa.accept_19_11_8_16_1_7988 11 65
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 65 225 5 2 13 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 65 225
  (Polychromatic418967fa.accept_17_9_14_4_1_3483 9 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 65 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 225 (accept_3_4 7 65 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 65 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 65 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 225 5 1 13 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 225 (accept_3_4 4 65 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 65 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 225
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 225 (accept_3_4 1 65 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 225 (allA_succ_of_accept 63 64 225
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 63 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 225 (accept_3_5 62 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 225 (Polychromatic418967fa.accept_13_8_12_4_1_4858 60 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 225 (accept_3_5 59 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 225 (Polychromatic418967fa.accept_14_2_8_1_1_1647 58 64 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 225
  (Polychromatic418967fa.accept_13_5_12_4_1_449 57 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 225 (accept_3_5 56 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 225 (Polychromatic418967fa.accept_12_6_4_9_1_544 54 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 225 (accept_3_5 53 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 225 (Polychromatic418967fa.accept_21_10_1_15_1_10541 52 64 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 225
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 225 (accept_3_5 50 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 225 (Polychromatic418967fa.accept_17_14_13_4_1_13402 48 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 225 (accept_3_5 47 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 64 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 225
  (Polychromatic418967fa.accept_21_3_1_15_1_4287 45 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 225 (accept_3_5 44 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 225 (Polychromatic418967fa.accept_12_6_4_9_1_544 42 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 225 (accept_3_5 41 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 225
  (Polychromatic418967fa.accept_10_9_4_5_1_616 39 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 225 (accept_3_5 38 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 225 (accept_3_5 35 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 225 (Polychromatic418967fa.accept_13_8_12_4_1_4858 34 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 225
  (Polychromatic418967fa.accept_13_7_12_4_1_450 33 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 225 (accept_3_5 32 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 225 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 225 (accept_3_5 29 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 225 (Polychromatic418967fa.accept_13_2_12_4_1_943 28 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 225
  (Polychromatic418967fa.accept_19_8_7_16_1_5117 27 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 225 (accept_3_5 26 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 225 (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 225 (accept_3_5 23 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 225 (Polychromatic418967fa.accept_20_2_4_5_1_13401 22 64
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 225
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 225 (accept_3_5 20 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 225 (accept_3_5 17 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 225
  (Polychromatic418967fa.accept_13_2_12_4_1_943 15 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 225 (accept_3_5 14 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 225 (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 225 (accept_3_5 11 64 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 225 (Polychromatic418967fa.accept_19_10_7_16_1_9311 10 64
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 225
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 225 (accept_3_5 8 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  225 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 64 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 225 (accept_3_5 5 64 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 225 (Polychromatic418967fa.accept_19_4_7_16_1_6486 4 64 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 225 (Polychromatic418967fa.accept_13_3_12_4_1_110 3
  64 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 225 (accept_3_5 2 64 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 225 (allA_succ_of_accept 62 63 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 225 3 20 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  59 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 225 3 19 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 225 (Polychromatic418967fa.accept_16_8_15_1_1_3006 56 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 63 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 225 9 6 7 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 225
  (Polychromatic418967fa.accept_12_5_3_9_1_541 53 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 225 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 225 3 17 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 225 3 16 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 225 9 5 7 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 225
  (Polychromatic418967fa.accept_30_14_3_15_1_13400 44 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 63 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 63 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 225 3 14 21 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 225
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 225 (Polychromatic418967fa.accept_16_8_15_1_1_3006 40 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 225 3 13 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 225
  (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 225 9 4 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 63 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 225 3 11 21 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 225
  (Polychromatic418967fa.accept_10_2_3_5_1_996 32 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 225 3 10 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 225 (Polychromatic418967fa.accept_12_5_3_9_1_541 29
  63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 225
  (Polychromatic418967fa.accept_10_8_3_5_1_613 28 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 225 9 3 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 225 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 63 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 225 3 8 21 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 225
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 225 3 7 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 225 (Polychromatic418967fa.accept_13_7_11_4_1_2247 20 63 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 225
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 225 9 2 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 225 (Polychromatic418967fa.accept_23_16_17_18_1_13399 16 63
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 225 3 5 21 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 225 3 4 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 225 9 1 7 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 225 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 225 3 2 21 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 225
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 225 (Polychromatic418967fa.accept_28_4_7_1_1_13398 4 63 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 225 3 1 21 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 225 (allA_succ_of_accept
  61 62 225 (accept_3_4 61 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 225
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 60 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 225 (accept_3_4 58 62 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 225
  (Polychromatic418967fa.accept_21_14_20_15_1_4285 56 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 62 225 (accept_3_4 55 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 62 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 62 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 62 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 62 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 225 (accept_3_4 52 62 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 51
  62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 225
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 50 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 225 (accept_3_4 49 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 225 (accept_3_4 46 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 225 (Polychromatic418967fa.accept_13_6_10_4_1_957 45 62 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 225 (accept_3_4 43 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 225 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 225 (accept_3_4 40 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 225 (accept_3_4 37 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 225 (Polychromatic418967fa.accept_16_4_14_1_1_1241 36 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 225 (accept_3_4 34 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 62 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 225
  (Polychromatic418967fa.accept_13_6_10_4_1_957 32 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 225 (accept_3_4 31 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 225 (accept_3_4 28 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 225 (accept_3_4 25 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 225 (Polychromatic418967fa.accept_13_11_10_4_1_1565 24 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 225 (accept_3_4 22 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 225 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 62 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 225
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 225 (accept_3_4 19 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 225 (accept_3_4 16 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 225
  (Polychromatic418967fa.accept_13_1_10_4_1_954 14 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 225 (accept_3_4 13 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 225 (accept_3_4 10 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 62 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 225 (accept_3_4 7 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  225 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 62 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 225 (accept_3_4 4 62 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 62
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 225 (accept_3_4 1 62 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 225 (allA_succ_of_accept 60 61 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 225 (accept_3_5 59 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 225 (Polychromatic418967fa.accept_13_5_9_4_1_441 57 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 225 (accept_3_5 56 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 225
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 225 (accept_3_5 53 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 225 (accept_3_5 50 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 225 (accept_3_5 47 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 225 (accept_3_5 44 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 225 (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 225
  (Polychromatic418967fa.accept_18_6_7_9_1_4250 42 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 225 (accept_3_5 41 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 225 (accept_3_5 38 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 225 (Polychromatic418967fa.accept_16_5_13_1_1_2084 37 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 225
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 225 (accept_3_5 35 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 225 (Polychromatic418967fa.accept_13_7_9_4_1_918 33 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 225 (accept_3_5 32 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 225
  (Polychromatic418967fa.accept_16_14_13_1_1_5278 30 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 225 (accept_3_5 29 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 225 (accept_3_5 26 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 225 (accept_3_5 23 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 225 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 225 (accept_3_5 20 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 61 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 225 (accept_3_5 17 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 225 (accept_3_5 14 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 225
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 225 (accept_3_5 11 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 225 (accept_3_5 8 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 225 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 61 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 225 (accept_3_5 5 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 61 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 225 (accept_3_5 2 61 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 225 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 61 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 225 (allA_succ_of_accept 59 60 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 60 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 225
  (Polychromatic418967fa.accept_19_1_3_16_1_9413 58 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 225 3 19 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 225 (Polychromatic418967fa.accept_16_8_12_1_1_7720 56 60 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 225 5 11 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 225 3 18 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 53
  60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 52 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 60 225 3 17 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 60 225 5 10 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 225 (Polychromatic418967fa.accept_13_10_8_4_1_3098 49 60 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 225 3 16 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 47
  60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 225
  (Polychromatic418967fa.accept_17_12_9_4_1_5982 46 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 60 225 15 3 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 60 225 (Polychromatic418967fa.accept_18_8_6_9_1_5576 44 60 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 225 (Polychromatic418967fa.accept_16_11_12_1_1_3001 43 60
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 225 3 14 20 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 225
  (Polychromatic418967fa.accept_21_20_18_15_1_11881 41 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 60 225 5 8 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 60 225 3 13 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 60 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 60 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 37
  60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 225 3 12 20 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 225 5 7 12 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 225
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 34 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 60 225 3 11 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 60 225 (Polychromatic418967fa.accept_18_14_6_9_1_1950 32 60 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 225 15 2 4 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 225
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 225 (Polychromatic418967fa.accept_21_7_18_15_1_2887 28 60 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 225 3 9 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 60 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 225 5 5 12 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 225 3 8 20 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 225
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 225 (Polychromatic418967fa.accept_13_9_8_4_1_937 22 60 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 225 3 7 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 225 5 4 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 225 3 6 20 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 225 (Polychromatic418967fa.accept_21_16_18_15_1_7282 16 60 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 225 15 1 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 225 (Polychromatic418967fa.accept_17_14_9_4_1_3465 14 60 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 225
  (Polychromatic418967fa.accept_8_5_4_1_1_111 13 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 225 3 4 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 225 (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 60 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 225 5 2 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 225 3 3 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 225 (Polychromatic418967fa.accept_16_8_12_1_1_7720 8 60 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 225
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 7 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 225 3 2 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 60 225 5 1 12 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 60 225 (Polychromatic418967fa.accept_16_4_12_1_1_1204 4 60 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 225 3 1 20 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 225 (Polychromatic418967fa.accept_16_2_12_1_1_3086 2 60 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 225
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 60 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 225 (allA_succ_of_accept 58
  59 225 (accept_3_4 58 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 225
  (Polychromatic418967fa.accept_23_11_13_18_1_3392 57 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 225 (accept_3_4 55 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 225 (accept_3_4 52 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 225 (accept_3_4 49 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 225 (Polychromatic418967fa.accept_13_9_7_4_1_953 48 59 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 225 (accept_3_4 46 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 225 (Polychromatic418967fa.accept_13_6_7_4_1_2264 45 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 225 (accept_3_4 43 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 225 (accept_3_4 40 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 225 (accept_3_4 37 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 225 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 59 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 225
  (Polychromatic418967fa.accept_13_9_7_4_1_953 35 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 225 (accept_3_4 34 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 225 (accept_3_4 31 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 225
  (Polychromatic418967fa.accept_13_3_7_4_1_435 29 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 225 (accept_3_4 28 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 225 (accept_3_4 25 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 59 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 225 (accept_3_4 22 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 225 (accept_3_4 19 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 225
  (Polychromatic418967fa.accept_19_17_2_16_1_7982 17 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 225 (accept_3_4 16 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 225 (accept_3_4 13 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 59 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 225 (accept_3_4 10 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 225 (accept_3_4 7 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 225 (accept_3_4 4 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  225 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 59 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 225 (accept_3_4 1 59 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 225
  (allA_succ_of_accept 57 58 225 (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 58 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 225 (accept_3_5 56 58 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 225 (Polychromatic418967fa.accept_12_6_10_9_1_531
  54 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 225 (accept_3_5 53
  58 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 52 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 225 (accept_3_5 50 58 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 48
  58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 225 (accept_3_5 47 58
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 225
  (Polychromatic418967fa.accept_13_7_6_4_1_933 46 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 58 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 225 (accept_3_5 44 58 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 225 (Polychromatic418967fa.accept_10_2_8_5_1_587
  42 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 225 (accept_3_5 41
  58 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 225
  (Polychromatic418967fa.accept_23_17_12_18_1_10092 40 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 225 (accept_3_5 38 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 225
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 225 (accept_3_5 35 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 225 (accept_3_5 32 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 225
  (Polychromatic418967fa.accept_11_8_3_5_1_355 30 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 225 (accept_3_5 29 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 225 (Polychromatic418967fa.accept_13_2_6_4_1_1593 28 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 225 (accept_3_5 26 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 225 (accept_3_5 23 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 225 (Polychromatic418967fa.accept_24_21_10_9_1_3044 21 58 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 225 (accept_3_5 20 58 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 225
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 225 (accept_3_5 17 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 225 (Polychromatic418967fa.accept_20_16_18_5_1_4638 16 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 225 (accept_3_5 14 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 225 (accept_3_5 11 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 225 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 225 (accept_3_5 8 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 225 (accept_3_5 5 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  225 (Polychromatic418967fa.accept_19_4_1_16_1_13397 4 58 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 225 (accept_3_5 2 58 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 225 (allA_succ_of_accept 56 57 225
  (Polychromatic418967fa.accept_16_8_9_1_1_7753 56 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 225 (Polychromatic418967fa.accept_18_1_3_9_1_328 55 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 225 3 18 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 53
  57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 225
  (Polychromatic418967fa.accept_10_2_7_5_1_605 52 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 225 3 17 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 225 (Polychromatic418967fa.accept_16_2_9_1_1_6404 50 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 225 (Polychromatic418967fa.accept_13_10_5_4_1_3107 49 57
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 225 3 16 19 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 225
  (Polychromatic418967fa.accept_27_20_3_9_1_13396 47 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 225 (Polychromatic418967fa.accept_22_2_13_5_1_13395 46 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 225 3 15 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 225 (Polychromatic418967fa.accept_17_10_6_4_1_2506
  44 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 225
  (Polychromatic418967fa.accept_10_3_7_5_1_288 43 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 225 3 14 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 225 (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 225 (Polychromatic418967fa.accept_13_1_5_4_1_463 40 57 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 225 3 13 19 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 225
  (Polychromatic418967fa.accept_10_8_7_5_1_602 38 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 225 (Polychromatic418967fa.accept_16_5_9_1_1_2070 37 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 225 3 12 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 225 (Polychromatic418967fa.accept_13_9_5_4_1_1591
  35 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 225
  (Polychromatic418967fa.accept_16_2_9_1_1_6404 34 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 225 3 11 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 225 (Polychromatic418967fa.accept_10_2_7_5_1_605 32 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 225 (Polychromatic418967fa.accept_18_13_3_9_1_4233 31 57
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 225 3 10 19 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 225
  (Polychromatic418967fa.accept_16_13_9_1_1_3022 29 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 225 3 9 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 225 (Polychromatic418967fa.accept_16_10_9_1_1_9973 26 57 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 225
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 25 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 225 3 8 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 225 (Polychromatic418967fa.accept_10_2_7_5_1_605 22 57 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 225 3 7 19 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 225
  (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 225 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 225 3 6 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 225 (Polychromatic418967fa.accept_27_17_3_9_1_13394 17 57
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 225
  (Polychromatic418967fa.accept_23_16_11_18_1_13393 16 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 57 225 3 5 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 57 225 (Polychromatic418967fa.accept_13_1_5_4_1_463 14 57 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 225 (Polychromatic418967fa.accept_10_3_7_5_1_288
  13 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 225 3 4 19 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 225
  (Polychromatic418967fa.accept_17_11_6_4_1_4729 11 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 225 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 225 3 3 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 57 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 225
  (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 225 3 2 19 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 225 (Polychromatic418967fa.accept_16_5_9_1_1_2070 5 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 225 (Polychromatic418967fa.accept_23_4_11_18_1_13392 4 57
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 225 3 1 19 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 225
  (Polychromatic418967fa.accept_10_2_7_5_1_605 2 57 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 225 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 57 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 225))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 225 (allA_succ_of_accept 55 56 225 (accept_3_4 55 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 225 (accept_3_4 52 56 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 225 (Polychromatic418967fa.accept_10_1_6_5_1_304
  51 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 225
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 50 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 225 (accept_3_4 49 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 225 (Polychromatic418967fa.accept_22_4_12_5_1_11851 48 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 225 (accept_3_4 46 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 225 (Polychromatic418967fa.accept_21_3_14_15_1_10526 45 56 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 225
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 225 (accept_3_4 43 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 225 (accept_3_4 40 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 225 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 56 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 225
  (Polychromatic418967fa.accept_20_18_16_5_1_9137 38 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 225 (accept_3_4 37 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 225 (Polychromatic418967fa.accept_16_4_8_1_1_5257 36 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 225 (accept_3_4 34 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 225 (Polychromatic418967fa.accept_17_16_5_4_1_2499 33 56 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 225
  (Polychromatic418967fa.accept_19_13_18_16_1_5123 32 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 56 225 (accept_3_4 31 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 56 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 56 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 225 (accept_3_4 28 56 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 225
  (Polychromatic418967fa.accept_19_8_18_16_1_7937 27 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 56 225 (Polychromatic418967fa.accept_21_5_14_15_1_7290 26 56 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 225 (accept_3_4 25 56 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 56 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 225 (accept_3_4 22 56
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 225
  (Polychromatic418967fa.accept_10_1_6_5_1_304 21 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 56 225 (Polychromatic418967fa.accept_16_4_8_1_1_5257 20 56 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 225 (accept_3_4 19 56 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 56 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 225 (accept_3_4 16 56
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 225
  (Polychromatic418967fa.accept_16_15_8_1_1_9959 15 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 56 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 56 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 225 (accept_3_4 13 56 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 56 225 (Polychromatic418967fa.accept_16_12_8_1_1_5270 12 56 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 56 225 (accept_3_4 10 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  56 225 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 56 225 (Polychromatic418967fa.accept_19_8_18_16_1_7937 8 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 225 (accept_3_4 7 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 56 225 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 56 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 56 225 (accept_3_4 4 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56
  225 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 56 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 56 225 (Polychromatic418967fa.accept_19_2_18_16_1_5111 2 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 225 (accept_3_4 1 56 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 56 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 225
  (allA_succ_of_accept 54 55 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 225 (accept_3_5 53 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 225 5 10 11 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 225
  (Polychromatic418967fa.accept_14_7_13_1_1_922 49 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 225 (Polychromatic418967fa.accept_20_8_15_5_1_2096 48 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 225 (accept_3_5 47 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 225 5 9 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 225 (accept_3_5 44 55 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 225 (Polychromatic418967fa.accept_20_3_15_5_1_10631 43 55 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 225 (accept_3_5 41 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  225 5 8 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 225 (accept_3_5 38 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 225 (Polychromatic418967fa.accept_20_16_15_5_1_7740 36 55
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 225 5 7 11 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 225 (accept_3_5 32 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 225 (Polychromatic418967fa.accept_20_11_15_5_1_10632 31 55 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 225 5 6 11 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 225 (accept_3_5 29 55 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 225
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 225 (accept_3_5 26 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  225 5 5 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 225 (Polychromatic418967fa.accept_16_8_7_1_1_8875 24 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 225 (accept_3_5 23 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 225 (Polychromatic418967fa.accept_14_7_13_1_1_922 21 55 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 225 5 4 11 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 225 (accept_3_5 17 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 225 5 3 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 225 (accept_3_5 14 55 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 225 (Polychromatic418967fa.accept_19_13_17_16_1_6479 13 55 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 225 (accept_3_5 11 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  225 5 2 11 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 225 (accept_3_5 8 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 225 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 225 5 1 11 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 225
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 225 (accept_3_5 2 55 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 225 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 55 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 225)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 225 (allA_succ_of_accept 53 54 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 54 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 52 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 54 225 3 17 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 54 225 (Polychromatic418967fa.accept_11_6_10_5_1_341 50 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 225 3 16 18 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 225 9 5 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 225 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 225 3 14 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 225 3 13 18 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 225 (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 225 9 4 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 34 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 54 225 3 11 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 54 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 225 3 10 18 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 225
  (Polychromatic418967fa.accept_10_9_4_5_1_616 29 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 225 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 225 9 3 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 225 3 8 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 225 3 7 18 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 225 9 2 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 225
  (Polychromatic418967fa.accept_10_6_4_5_1_615 16 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 54 225 3 5 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 54 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 225 3 4 18 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 225 9 1 6 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 225 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 225 3 2 18 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 225 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 54 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 225 3 1 18 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 225
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 54 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 225 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 54 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 225)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  225 (allA_succ_of_accept 52 53 225 (accept_3_4 52 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 51 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 225 (accept_3_4 49 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 225 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 53 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 225 (accept_3_4 46 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 225 (accept_3_4 43 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 225 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 53 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 225
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 41 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 225 (accept_3_4 40 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 225 (accept_3_4 37 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 53 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 225
  (Polychromatic418967fa.accept_20_15_13_5_1_6061 35 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 225 (accept_3_4 34 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 225 (accept_3_4 31 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 225 (Polychromatic418967fa.accept_18_12_17_9_1_5513 30 53 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 225
  (Polychromatic418967fa.accept_11_7_9_5_1_338 29 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 225 (accept_3_4 28 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 225 (accept_3_4 25 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 53 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 225
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 225 (accept_3_4 22 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 225 (Polychromatic418967fa.accept_27_21_26_9_1_13391 21 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 225 (accept_3_4 19 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 225 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 53 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 225 (accept_3_4 16 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 225 (accept_3_4 13 53 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 53 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 225
  (Polychromatic418967fa.accept_19_11_15_16_1_9396 11 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 53 225 (accept_3_4 10 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 53 225 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 53 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 225 (accept_3_4 7 53 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 225 (Polychromatic418967fa.accept_16_6_5_1_1_7761 6
  53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 225 (accept_3_4 4 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  225 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 53 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 225 (accept_3_4 1 53 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 225))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 225
  (allA_succ_of_accept 51 52 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 225 (accept_3_5 50 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 225 (Polychromatic418967fa.accept_10_8_2_5_1_596
  48 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 225 (accept_3_5 47
  52 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 46 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 225 (accept_3_5 44 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 225 (Polychromatic418967fa.accept_12_6_4_9_1_544
  42 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 225 (accept_3_5 41
  52 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 52 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 225 (accept_3_5 38 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 52 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 225 (Polychromatic418967fa.accept_11_3_8_5_1_336
  36 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 225 (accept_3_5 35
  52 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 225
  (Polychromatic418967fa.accept_23_11_6_18_1_8446 34 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 52 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 225 (accept_3_5 32 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 52 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 30
  52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 225 (accept_3_5 29 52
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 52 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 225 (accept_3_5 26 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 52 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219
  24 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 225 (accept_3_5 23
  52 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 225
  (Polychromatic418967fa.accept_17_5_1_4_1_3460 22 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 52 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 225 (accept_3_5 20 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 52 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 18
  52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 225 (accept_3_5 17 52
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 225 (Polychromatic418967fa.accept_7_2_3_1_1_10
  16 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 225
  (Polychromatic418967fa.accept_18_15_16_9_1_4299 15 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 225 (accept_3_5 14 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 52 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 225 (accept_3_5 11 52 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 225 (Polychromatic418967fa.accept_20_10_12_5_1_4687 10 52 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 225 (accept_3_5 8 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  225 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 225 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 225 (accept_3_5 5 52 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 52 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 225 (Polychromatic418967fa.accept_10_3_2_5_1_295 3
  52 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 225 (accept_3_5 2 52 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  225)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 225 (allA_succ_of_accept 50 51 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 225 3 16 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  47 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 225 3 15 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 51 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 225 3 14 17 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 225 (Polychromatic418967fa.accept_18_4_15_9_1_6882 40 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 225 3 13 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 225 3 12 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 225 3 11 17 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 225
  (Polychromatic418967fa.accept_21_11_9_15_1_5746 32 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 225 3 10 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 29
  51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 225
  (Polychromatic418967fa.accept_13_2_12_4_1_943 28 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 225 3 9 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 51 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 225 3 8 17 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 225
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 225 3 7 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 51 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 225
  (Polychromatic418967fa.accept_10_9_1_5_1_594 19 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 225 3 6 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 225 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 51 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 225 3 5 17 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 225 3 4 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 51 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 225 3 3 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 225 (Polychromatic418967fa.accept_13_8_12_4_1_4858 8 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 225 3 2 17 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 225
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 51 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 225 3 1 17 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 51 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 225))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 225 (allA_succ_of_accept 49 50 225
  (accept_3_4 49 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 225
  (Polychromatic418967fa.accept_20_8_10_5_1_6083 48 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 225 (accept_3_4 46 50 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 50 225 5 9 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 50 225 (Polychromatic418967fa.accept_14_2_8_1_1_1647 44 50 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 225 (accept_3_4 43 50 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 50 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 50 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 225 5 8 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 225 (Polychromatic418967fa.accept_13_12_11_4_1_3111 38 50
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 225 (accept_3_4 37 50 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 225
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 50 225 5 7 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 50 225 (accept_3_4 34 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  50 225 (Polychromatic418967fa.accept_13_7_11_4_1_2247 33 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 50 225 (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 50 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 225 (accept_3_4 31 50 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 225 5 6 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 225 (accept_3_4 28 50 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 225
  (Polychromatic418967fa.accept_19_7_12_16_1_9393 26 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 225 25 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 225 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 50 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 225 (accept_3_4 22 50 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 225 (Polychromatic418967fa.accept_11_10_6_5_1_1239
  21 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 225 5 4 10 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 225 (accept_3_4 19
  50 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 225
  (Polychromatic418967fa.accept_12_6_2_9_1_537 18 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 225 (accept_3_4 16 50 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 50 225 5 3 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 50 225 (Polychromatic418967fa.accept_19_14_12_16_1_7952 14 50 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 225 (accept_3_4 13 50 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 225 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 50 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 225 5 2 10 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 225 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 50 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 225 (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 50 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 225 (accept_3_4 7 50 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 225 (Polychromatic418967fa.accept_12_6_2_9_1_537 6
  50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 225 5 1 10 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 225 (accept_3_4 4 50
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 225 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 225
  (Polychromatic418967fa.accept_13_2_11_4_1_445 2 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 225 (accept_3_4 1 50 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  225)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 225 (allA_succ_of_accept 48 49 225
  (Polychromatic418967fa.accept_14_6_7_1_1_78 48 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 225 (accept_3_5 47 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 225 (Polychromatic418967fa.accept_13_6_10_4_1_957 45 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 225 (accept_3_5 44 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 225 (Polychromatic418967fa.accept_19_5_11_16_1_8010 43 49 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 225
  (Polychromatic418967fa.accept_18_6_13_9_1_4218 42 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 225 (accept_3_5 41 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 225 (accept_3_5 38 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 225 (Polychromatic418967fa.accept_13_11_10_4_1_1565 37 49 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 225
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 225 (accept_3_5 35 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 225 (Polychromatic418967fa.accept_13_7_10_4_1_919 33 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 225 (accept_3_5 32 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 225
  (Polychromatic418967fa.accept_20_10_9_5_1_3327 30 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 225 (accept_3_5 29 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 225 (accept_3_5 26 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 225 (Polychromatic418967fa.accept_19_6_11_16_1_9391 25 49 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 225
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 225 (accept_3_5 23 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 225 (accept_3_5 20 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 225 (Polychromatic418967fa.accept_13_6_10_4_1_957 19 49 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 225
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 225 (accept_3_5 17 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 225 (accept_3_5 14 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 225 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 49 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 225
  (Polychromatic418967fa.accept_21_12_7_15_1_7272 12 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 225 (accept_3_5 11 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 225 (Polychromatic418967fa.accept_21_9_7_15_1_5769 9 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 225 (accept_3_5 8 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 225 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 49 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 225
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 225 (accept_3_5 5 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 49 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 225 (accept_3_5 2 49 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 49 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 225))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 225 (allA_succ_of_accept 47 48 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 48 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 225 (Polychromatic418967fa.accept_13_7_9_4_1_918
  46 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 225 3 15 16 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 43 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 225 3 14 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 225 (Polychromatic418967fa.accept_17_7_14_4_1_4745
  41 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 225 3 13 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 225 (Polychromatic418967fa.accept_21_17_6_15_1_5765 38 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 225 3 12 16 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 225
  (Polychromatic418967fa.accept_14_7_6_1_1_1656 35 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 225 (Polychromatic418967fa.accept_13_8_9_4_1_1552 34 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 225 3 11 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 32
  48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 225
  (Polychromatic418967fa.accept_13_5_9_4_1_441 31 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 225 3 10 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 225 (Polychromatic418967fa.accept_18_11_12_9_1_992 29 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 225 (Polychromatic418967fa.accept_18_10_12_9_1_2012 28 48
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 225 3 9 16 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 225 (Polychromatic418967fa.accept_19_6_10_16_1_7989 25 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 225 3 8 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 48 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 225
  (Polychromatic418967fa.accept_10_2_8_5_1_587 22 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 225 3 7 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 225 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 225 3 6 16 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 225
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 225 3 5 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 225 (Polychromatic418967fa.accept_20_14_8_5_1_6090 14 48 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 225
  (Polychromatic418967fa.accept_10_3_8_5_1_606 13 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 225 3 4 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 225 (Polychromatic418967fa.accept_18_11_12_9_1_992 11 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 225 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 48 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 225 3 3 16 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 225
  (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 225 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 225 3 2 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 48 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 225
  (Polychromatic418967fa.accept_18_4_12_9_1_2011 4 48 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 225 3 1 16 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 48 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 225 (Polychromatic418967fa.accept_17_1_14_4_1_1550 1 48 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  225)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 225 (allA_succ_of_accept 46 47 225 (accept_3_4 46 47
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 225 (Polychromatic418967fa.accept_7_3_5_1_1_72
  45 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 225
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 225 (accept_3_4 43 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 225 (accept_3_4 40 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 47 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 225 (accept_3_4 37 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 225 (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 225 (Polychromatic418967fa.accept_13_9_8_4_1_937 35 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 225 (accept_3_4 34 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 47 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 225
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 225 (accept_3_4 31 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 225 (Polychromatic418967fa.accept_19_10_9_16_1_5085 29 47 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 225 (accept_3_4 28 47 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 47 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 225 (accept_3_4 25 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 225 (accept_3_4 22 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 225 (Polychromatic418967fa.accept_16_5_15_1_1_2113 21 47 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 225
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 225 (accept_3_4 19 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 225 (accept_3_4 16 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 47 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 225 (accept_3_4 13 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 225 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 225 (accept_3_4 10 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 225 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 47 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 225
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 225 (accept_3_4 7 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 225 (Polychromatic418967fa.accept_16_5_15_1_1_2113 5 47 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 225 (accept_3_4 4 47 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 47 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 225 (accept_3_4 1 47 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 225))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  225 (allA_succ_of_accept 45 46 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 225 (accept_3_5 44 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 225 (Polychromatic418967fa.accept_12_6_10_9_1_531
  42 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 225 (accept_3_5 41
  46 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 40 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 225 (accept_3_5 38 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 225 (Polychromatic418967fa.accept_13_10_7_4_1_2262
  36 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 225 (accept_3_5 35
  46 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 225
  (Polychromatic418967fa.accept_10_4_6_5_1_74 34 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 225 (accept_3_5 32 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 225 (Polychromatic418967fa.accept_11_8_2_5_1_1769
  30 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 225 (accept_3_5 29
  46 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 225
  (Polychromatic418967fa.accept_19_9_8_16_1_5101 28 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 225 (accept_3_5 26 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 225 (accept_3_5 23 46
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 225
  (Polychromatic418967fa.accept_13_9_7_4_1_953 22 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 225 (accept_3_5 20 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 225 (Polychromatic418967fa.accept_12_6_10_9_1_531
  18 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 225 (accept_3_5 17
  46 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 225
  (Polychromatic418967fa.accept_13_3_7_4_1_435 16 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 225 (accept_3_5 14 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 12
  46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 225 (accept_3_5 11 46
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 225 (Polychromatic418967fa.accept_7_3_4_1_1_71
  10 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 225
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 225 (accept_3_5 8 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 225 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 225 (accept_3_5 5 46 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 46 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 225 (accept_3_5 2 46 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  225)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 225 (allA_succ_of_accept 44 45 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 45 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 225 (Polychromatic418967fa.accept_21_1_3_15_1_5797 43 45 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 225 3 14 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 225 (Polychromatic418967fa.accept_13_2_6_4_1_1593
  41 45 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 225 5 8 9 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 45 225 3 13 15 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 225
  (Polychromatic418967fa.accept_21_17_3_15_1_5762 38 45 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 45 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 225 9 4 5 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 45 225 5 7 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 225 (Polychromatic418967fa.accept_22_12_1_5_1_13390 34 45
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 225 3 11 15 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 45 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 225 (Polychromatic418967fa.accept_13_5_6_4_1_1582 31 45 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 225 15 2 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 225 (Polychromatic418967fa.accept_19_10_7_16_1_9311 29 45
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 225
  (Polychromatic418967fa.accept_8_4_5_1_1_299 28 45 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 225 9 3 5 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 45 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 225 5 5 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 225 3 8 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 45 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 225
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 22 45 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 225 3 7 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 45 225 5 4 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 45 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 225 9 2 5 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 225 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 45 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 45 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 225 15 1 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 225 (Polychromatic418967fa.accept_16_14_13_1_1_5278 14 45 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 225 (Polychromatic418967fa.accept_27_13_18_9_1_13389 13 45
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 225 3 4 15 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 45 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 225 5 2 9 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 45 225 9 1 5 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 225 (Polychromatic418967fa.accept_19_8_7_16_1_5117 8 45 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 225 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 45 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 225 3 2 15 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 45 225 5 1 9 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 45 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 225 3 1 15 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 45 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 225 (Polychromatic418967fa.accept_21_1_3_15_1_5797 1 45 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  225))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 225 (allA_succ_of_accept 43 44 225 (accept_3_4 43 44
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 225
  (Polychromatic418967fa.accept_12_6_8_9_1_553 42 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 225 (accept_3_4 40 44 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 38
  44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 225 (accept_3_4 37 44
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 225
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 225 (accept_3_4 34 44 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 225 (Polychromatic418967fa.accept_27_6_17_9_1_13388 33 44 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 225
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 32 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 225 (accept_3_4 31 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 225 (accept_3_4 28 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 44 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 225
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 225 (accept_3_4 25 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 225 (accept_3_4 22 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 44 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 225 (accept_3_4 19 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 225 (accept_3_4 16 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 225 (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 44 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 225
  (Polychromatic418967fa.accept_13_1_5_4_1_463 14 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 225 (accept_3_4 13 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 225 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 225 (accept_3_4 10 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 44 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 225
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 225 (accept_3_4 7 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  225 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 225 (accept_3_4 4 44 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 44 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 225 (Polychromatic418967fa.accept_13_2_5_4_1_3926 2
  44 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 225 (accept_3_4 1 44 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 225)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  225 (allA_succ_of_accept 42 43 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 225 (accept_3_5 41 43 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 225 (Polychromatic418967fa.accept_11_6_10_5_1_341
  39 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 225 (accept_3_5 38
  43 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 225
  (Polychromatic418967fa.accept_10_7_3_5_1_301 37 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 43 225 (Polychromatic418967fa.accept_17_2_9_4_1_3463 36 43 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 225 (accept_3_5 35 43 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 43 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 225
  (Polychromatic418967fa.accept_19_14_5_16_1_7940 33 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 225 (accept_3_5 32 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 225 (Polychromatic418967fa.accept_16_15_11_1_1_7767 31 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 225 (accept_3_5 29 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 225
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 225 (accept_3_5 26 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 225 (Polychromatic418967fa.accept_23_2_20_18_1_13387 25 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 225 (Polychromatic418967fa.accept_18_6_7_9_1_4250 24 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 225 (accept_3_5 23 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 225
  (Polychromatic418967fa.accept_18_3_7_9_1_5486 21 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 225 (accept_3_5 20 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 225 (Polychromatic418967fa.accept_17_2_9_4_1_3463 19 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 225 (accept_3_5 17 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 225
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 225 (accept_3_5 14 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 225 (Polychromatic418967fa.accept_17_13_9_4_1_5979 13 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 225 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 225 (accept_3_5 11 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 225
  (Polychromatic418967fa.accept_28_9_15_1_1_13386 9 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 225 (accept_3_5 8 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  225 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 225 (accept_3_5 5 43 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3
  43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 225 (accept_3_5 2 43 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 225 (Polychromatic418967fa.accept_19_1_5_16_1_2587
  1 43 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  225))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 225 (allA_succ_of_accept 41 42 225
  (Polychromatic418967fa.accept_16_9_10_1_1_2998 41 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 42 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 225 3 13 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 38
  42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 225
  (Polychromatic418967fa.accept_10_7_2_5_1_298 37 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 225 3 12 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 42 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 225 3 11 14 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 225
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 225 3 10 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 29
  42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 42 225 3 9 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 42 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 42 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 225 (Polychromatic418967fa.accept_13_12_3_4_1_928 25 42 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 225 3 8 14 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 42 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 225 3 7 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 225 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 225 3 6 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 42 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 42 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 225 3 5 14 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 225
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 225 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 42 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 225 3 4 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 225
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 42 225 3 3 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 42 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 42 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 225 3 2 14 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 225
  (Polychromatic418967fa.accept_27_5_15_9_1_13385 5 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 42 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 225 3 1 14 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 42 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 225
  (Polychromatic418967fa.accept_13_1_3_4_1_925 1 42 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 225)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 225 (allA_succ_of_accept 40 41 225
  (accept_3_4 40 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 225
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 225 (accept_3_4 37 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 225 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 41 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 225 (Polychromatic418967fa.accept_11_2_8_5_1_1219
  35 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 225 (accept_3_4 34
  41 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 225 (accept_3_4 31 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 41 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 225 (Polychromatic418967fa.accept_10_9_1_5_1_594
  29 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 225 (accept_3_4 28
  41 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 225
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 225 (accept_3_4 25 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 41 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 23
  41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 225 (accept_3_4 22 41
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 225
  (Polychromatic418967fa.accept_14_7_13_1_1_922 21 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 225 (accept_3_4 19 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 225 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 41 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 225
  (Polychromatic418967fa.accept_19_17_3_16_1_13384 17 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 41 225 (accept_3_4 16 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 41 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 225 (accept_3_4 13 41 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 12
  41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 225
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 225 (accept_3_4 10 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 225 (accept_3_4 7 41 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 225 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 41 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 225 (accept_3_4 4 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  225 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 41 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 225 (accept_3_4 1 41 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 225))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 225 (allA_succ_of_accept 39 40 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 225 (accept_3_5 38 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 225 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 40 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 225 5 7 8 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 34 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 40 225 (Polychromatic418967fa.accept_18_15_4_9_1_4204 33 40 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 225 (accept_3_5 32 40 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 40 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 225 5 6 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 225 (accept_3_5 29 40 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 225 (Polychromatic418967fa.accept_16_12_8_1_1_5270 28 40 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 225 (accept_3_5 26 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40
  225 5 5 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  40 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 40 225 (accept_3_5 23 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 40 225 (Polychromatic418967fa.accept_17_5_6_4_1_8607 22 40 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 225 (Polychromatic418967fa.accept_27_21_13_9_1_13383 21 40
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 225 5 4 8 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 225
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 40 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 40 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 225 (accept_3_5 17 40 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 40 225 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 40 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 40 225 5 3 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 40 225 (accept_3_5 14 40 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 225
  (Polychromatic418967fa.accept_16_12_8_1_1_5270 12 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 225 (accept_3_5 11 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  225 5 2 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40
  225 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 225 (accept_3_5 8 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  225 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 40 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 40 225 5 1 8 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 40 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 40 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 225 (accept_3_5 2 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 225)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 225 (allA_succ_of_accept 38 39 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 39 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 225 3 12 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 225 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 225 3 11 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 225 (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 39 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 39 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 225 3 10 13 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 225
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 225 (Polychromatic418967fa.accept_21_7_18_15_1_2887 28 39 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 225 3 9 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 225 3 8 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 225 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 39 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 225 3 7 13 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 225
  (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 39 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 225 3 6 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 39 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 225
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 225 3 5 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 39 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 225 3 4 13 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 225 3 3 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 225 (Polychromatic418967fa.accept_16_8_7_1_1_8875 8 39 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 225
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 225 3 2 13 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 39 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 39 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 225 3 1 13 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 39 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 225))))))))))))))))))))))))))))))))))))))) (allB_succ 38 225
  (allA_succ_of_accept 37 38 225 (accept_3_4 37 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 225 (Polychromatic418967fa.accept_20_16_18_5_1_4638 36 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 225 (accept_3_4 34 38 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 38 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 225 (accept_3_4 31 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 225 (accept_3_4 28 38 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 225 (accept_3_4 25 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 225 (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 225 (accept_3_4 22 38 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 225 (Polychromatic418967fa.accept_13_8_12_4_1_4858 21 38 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 225
  (Polychromatic418967fa.accept_13_7_12_4_1_450 20 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 225 (accept_3_4 19 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 225 (accept_3_4 16 38 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 225
  (Polychromatic418967fa.accept_21_14_17_15_1_9017 14 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 38 225 (accept_3_4 13 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 38 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 38 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 225 (accept_3_4 10 38 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 38
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 225
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 8 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 225 (accept_3_4 7 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  225 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 38 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 225 (accept_3_4 4 38 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 38
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 225 (accept_3_4 1 38 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 225)))))))))))))))))))))))))))))))))))))) (allB_succ 37 225
  (allA_succ_of_accept 36 37 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 225 (accept_3_5 35 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 225 (Polychromatic418967fa.accept_10_3_7_5_1_288
  33 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 225 (accept_3_5 32
  37 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 225
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 225 (Polychromatic418967fa.accept_17_13_3_4_1_2537 30 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 225 (accept_3_5 29 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 27
  37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 225 (accept_3_5 26 37
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 225
  (Polychromatic418967fa.accept_13_12_11_4_1_3111 25 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 225 (accept_3_5 23 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 225 (Polychromatic418967fa.accept_11_10_4_5_1_359
  21 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 225 (accept_3_5 20
  37 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 225
  (Polychromatic418967fa.accept_13_6_11_4_1_938 19 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 225 (accept_3_5 17 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 225 (Polychromatic418967fa.accept_12_3_1_9_1_202
  15 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 225 (accept_3_5 14
  37 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 225 (accept_3_5 11 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 225 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9
  37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 225 (accept_3_5 8 37 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 225 (Polychromatic418967fa.accept_13_7_11_4_1_2247
  7 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 225
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 225 (accept_3_5 5 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 225 (accept_3_5 2 37 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 225 (Polychromatic418967fa.accept_21_1_16_15_1_8913 1 37 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 225))))))))))))))))))))))))))))))))))))) (allB_succ 36 225
  (allA_succ_of_accept 35 36 225 (Polychromatic418967fa.accept_14_7_8_1_1_1621 35 36 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 36 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 225 3 11 12 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 225
  (Polychromatic418967fa.accept_13_6_10_4_1_957 32 36 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 36 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 225 3 10 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 29
  36 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 225
  (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 36 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 225 9 3 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 225 (Polychromatic418967fa.accept_17_9_2_4_1_3472 26 36 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 225 (Polychromatic418967fa.accept_22_3_14_5_1_13382 25 36
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 225 3 8 12 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 225
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 23 36 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 225 (Polychromatic418967fa.accept_19_3_17_16_1_6495 22 36 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 225 3 7 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 225 (Polychromatic418967fa.accept_13_7_10_4_1_919 20 36 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 225
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 36 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 225 9 2 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 225 (Polychromatic418967fa.accept_22_17_14_5_1_7064 17 36 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 225 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 36 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 225 3 5 12 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 225
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 36 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 225 3 4 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 36 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 225
  (Polychromatic418967fa.accept_20_10_16_5_1_3311 10 36 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 225 9 1 4 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 225 (Polychromatic418967fa.accept_11_8_3_5_1_355 8 36 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 225 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 36 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 225 3 2 12 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 225
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 36 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 36 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 225 3 1 12 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 225 (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 36 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 225
  (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 225)))))))))))))))))))))))))))))))))))) (allB_succ 35 225 (allA_succ_of_accept 34 35 225 (accept_3_4 34
  35 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 225
  (Polychromatic418967fa.accept_13_7_9_4_1_918 33 35 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 225 (accept_3_4 31 35 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 225 5 6 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 225 (Polychromatic418967fa.accept_16_13_3_1_1_2100 29 35 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 225 (accept_3_4 28 35 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 225 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 35 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 225 5 5 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 225 (Polychromatic418967fa.accept_20_4_15_5_1_10633 24 35 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 225 (Polychromatic418967fa.accept_20_3_15_5_1_10631 23 35
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 225 (accept_3_4 22 35 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 225 (Polychromatic418967fa.accept_13_8_9_4_1_1552
  21 35 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 225 5 4 7 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 225 (accept_3_4 19
  35 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 225 (Polychromatic418967fa.accept_20_17_15_5_1_4627 17 35 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 225 (accept_3_4 16 35 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 225 5 3 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 225 (accept_3_4 13 35 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 225 (Polychromatic418967fa.accept_18_12_17_9_1_5513 12 35 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 225
  (Polychromatic418967fa.accept_20_11_15_5_1_10632 11 35 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 35 225 5 2 7 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 35 225 (Polychromatic418967fa.accept_20_9_15_5_1_4670 9 35 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 225 (accept_3_4 7 35 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 225 5 1 7 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 225 (accept_3_4 4 35
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 225
  (Polychromatic418967fa.accept_12_3_11_9_1_193 3 35 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 225 (accept_3_4 1 35 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 225))))))))))))))))))))))))))))))))))) (allB_succ 34 225 (allA_succ_of_accept 33 34 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 225 (accept_3_5 32 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 34 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 225 (accept_3_5 29 34 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 225 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 34 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 225 (accept_3_5 26 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 225 (Polychromatic418967fa.accept_13_11_8_4_1_3950 24 34 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 225 (accept_3_5 23 34 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 225 (Polychromatic418967fa.accept_13_9_8_4_1_937 22 34 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 225
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 225 (accept_3_5 20 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 225 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 34 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 225 (accept_3_5 17 34 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 34 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 225 (accept_3_5 14 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 34 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 225 (accept_3_5 11 34 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 225 (Polychromatic418967fa.accept_13_10_8_4_1_3098 10 34 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 225 (accept_3_5 8 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 225 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 34 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 225 (accept_3_5 5 34 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 225 (Polychromatic418967fa.accept_22_4_12_5_1_11851 4 34 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 225 (accept_3_5 2 34 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 225))))))))))))))))))))))))))))))))))
  (allB_succ 33 225 (allA_succ_of_accept 32 33 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 33 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 33 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 225 3 10 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 225 (Polychromatic418967fa.accept_13_3_7_4_1_435 29 33 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 225 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 33 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 225 3 9 11 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 225
  (Polychromatic418967fa.accept_21_5_12_15_1_11875 26 33 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 33 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 33 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 225 3 8 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 225 (Polychromatic418967fa.accept_13_10_7_4_1_2262
  23 33 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 225
  (Polychromatic418967fa.accept_10_2_3_5_1_996 22 33 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 225 3 7 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 33 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 225 (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 33 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 225 3 6 11 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 33 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 225 (Polychromatic418967fa.accept_13_3_7_4_1_435 16 33 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 225 3 5 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 225 (Polychromatic418967fa.accept_21_14_12_15_1_7299 14 33
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 225
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 33 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 225 3 4 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 33 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 33 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 225 3 3 11 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 225
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 33 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 33 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 225 3 2 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 225 (Polychromatic418967fa.accept_17_5_16_4_1_4734 5 33 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 33 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 225 3 1 11 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 225 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 33 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 225 (Polychromatic418967fa.accept_21_1_12_15_1_2880 1 33 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 225)))))))))))))))))))))))))))))))))
  (allB_succ 32 225 (allA_succ_of_accept 31 32 225 (accept_3_4 31 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 32 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 225 (accept_3_4 28 32 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 225 (Polychromatic418967fa.accept_10_7_2_5_1_298
  27 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 225 (accept_3_4 25 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 225 (accept_3_4 22 32 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 225 (Polychromatic418967fa.accept_18_3_14_9_1_4264 21 32 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 225
  (Polychromatic418967fa.accept_13_7_6_4_1_933 20 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 225 (accept_3_4 19 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 225 (accept_3_4 16 32 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 225 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 32 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 225
  (Polychromatic418967fa.accept_19_14_13_16_1_9318 14 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 32 225 (accept_3_4 13 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 32 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 32 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 225 (accept_3_4 10 32 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 225 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9
  32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 225 (accept_3_4 7 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  225 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 32 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 225 (accept_3_4 4 32 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 32 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 32 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 225
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 2 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 32 225 (accept_3_4 1 32 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  225)))))))))))))))))))))))))))))))) (allB_succ 31 225 (allA_succ_of_accept 30 31 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 225 (accept_3_5 29 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 31 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 225 (accept_3_5 26 31 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 31 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 225
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 225 (accept_3_5 23 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 225 (Polychromatic418967fa.accept_16_5_15_1_1_2113 21 31 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 225 (accept_3_5 20 31 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 225 (accept_3_5 17 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 31 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 225 (accept_3_5 14 31 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 225 (Polychromatic418967fa.accept_17_13_14_4_1_2468 13 31 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 225 (accept_3_5 11 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 31 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 225 (accept_3_5 8 31 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 31 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 225 (accept_3_5 5 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 31 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 225 (accept_3_5 2 31 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 225 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 31 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 225))))))))))))))))))))))))))))))) (allB_succ 30 225
  (allA_succ_of_accept 29 30 225 (Polychromatic418967fa.accept_16_13_14_1_1_2094 29 30 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 30 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 225 3 9 10 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 225
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 30 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 30 225 5 5 6 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 30 225 3 8 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 225 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 30 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 225 3 7 10 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 225 5 4 6 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 225 3 6 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 30 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 30 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 225 15 1 2 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 225
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 30 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 30 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 225 3 4 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 225 5 2 6 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 225 3 3 10 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 225
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 30 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 225 3 2 10 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 225 5 1 6 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 30 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 225 3 1 10 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 225
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 30 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 225 (Polychromatic418967fa.accept_20_1_10_5_1_6044 1 30 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 225)))))))))))))))))))))))))))))) (allB_succ 29 225 (allA_succ_of_accept
  28 29 225 (accept_3_4 28 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 225
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 225 (accept_3_4 25 29 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 29 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 225
  (Polychromatic418967fa.accept_19_4_10_16_1_6531 23 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 225 (accept_3_4 22 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 225 (accept_3_4 19 29 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 225 (Polychromatic418967fa.accept_21_18_8_15_1_5745 18 29 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 225
  (Polychromatic418967fa.accept_21_17_8_15_1_10549 17 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 29 225 (accept_3_4 16 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 29 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 29 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 225 (accept_3_4 13 29 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 12
  29 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 225
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 225 (accept_3_4 10 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 225 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 225 (accept_3_4 7 29 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 225 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 29 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 225
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 5 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 225 (accept_3_4 4 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  225 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 29 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 225 (accept_3_4 1 29 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 225))))))))))))))))))))))))))))) (allB_succ 28 225 (allA_succ_of_accept 27 28 225
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 225 (accept_3_5 26 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 225 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 28 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 225 (accept_3_5 23 28 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 28 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 225
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 225 (accept_3_5 20 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 225 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 225 (accept_3_5 17 28 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 225 (Polychromatic418967fa.accept_23_16_5_18_1_13381 16 28 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 225
  (Polychromatic418967fa.accept_17_15_11_4_1_7218 15 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 225 (accept_3_5 14 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 28 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 225 (accept_3_5 11 28 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 225 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 28 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 225
  (Polychromatic418967fa.accept_21_9_7_15_1_5769 9 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 225 (accept_3_5 8 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  225 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 225 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 28 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 225 (accept_3_5 5 28 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 225 (Polychromatic418967fa.accept_16_4_12_1_1_1204 4 28 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 225 (Polychromatic418967fa.accept_10_3_8_5_1_606 3
  28 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 225 (accept_3_5 2 28 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 225))))))))))))))))))))))))))))
  (allB_succ 27 225 (allA_succ_of_accept 26 27 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 27 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 225 3 8 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 27 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 225 3 7 9 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 225
  (Polychromatic418967fa.accept_19_1_8_16_1_6488 20 27 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 27 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 225 9 2 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 225 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 27 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 225
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 27 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 225 3 5 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 225 3 4 9 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 225
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 27 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 225 9 1 3 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 225 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 27 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 225
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 225 3 2 9 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 27 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 225 (Polychromatic418967fa.accept_21_4_6_15_1_5744 4 27 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 225 3 1 9 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 27 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 225))))))))))))))))))))))))))) (allB_succ 26 225 (allA_succ_of_accept 25
  26 225 (accept_3_4 25 26 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 225
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 26 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 225 (accept_3_4 22 26 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 225 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 26 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  26 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 225 (accept_3_4 19 26
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 26 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 225 (accept_3_4 16 26 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 14
  26 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 225 (accept_3_4 13 26
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 225
  (Polychromatic418967fa.accept_17_12_9_4_1_5982 12 26 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 225 (accept_3_4 10 26 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 225 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 26 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 225 (Polychromatic418967fa.accept_19_8_7_16_1_5117
  8 26 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 225 (accept_3_4 7 26
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 225 (Polychromatic418967fa.accept_7_6_5_1_1_416
  6 26 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 225 (accept_3_4 4 26 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 225 (Polychromatic418967fa.accept_17_2_9_4_1_3463 2 26 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 225 (accept_3_4 1 26 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 225)))))))))))))))))))))))))) (allB_succ 25 225 (allA_succ_of_accept 24 25 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 225 (accept_3_5 23 25 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 225 (Polychromatic418967fa.accept_13_8_12_4_1_4858 21 25 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 225 5 4 5 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 25 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 225 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 25 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 225 (accept_3_5 17 25 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 25 225 5 3 5 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 25 225 (accept_3_5 14 25 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 225 (Polychromatic418967fa.accept_16_13_9_1_1_3022 13 25 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 225 (accept_3_5 11 25 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25
  225 5 2 5 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25
  225 (Polychromatic418967fa.accept_19_9_6_16_1_5116 9 25 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 25 225 (accept_3_5 8 25 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 25 225 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 25 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 225 (Polychromatic418967fa.accept_18_6_7_9_1_4250 6 25 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 25 225 5 1 5 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 25 225
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 25 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 225 (accept_3_5 2 25 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 225 (Polychromatic418967fa.accept_17_1_8_4_1_1519 1 25 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 225))))))))))))))))))))))))) (allB_succ 24 225
  (allA_succ_of_accept 23 24 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 24 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 225 (Polychromatic418967fa.accept_19_3_5_16_1_13380 22 24
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 225 3 7 8 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 225
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 20 24 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 225 3 6 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 225 (Polychromatic418967fa.accept_21_17_3_15_1_5762 17 24
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 24 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 225 3 5 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 225 (Polychromatic418967fa.accept_17_14_7_4_1_3476 14 24 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 225 (Polychromatic418967fa.accept_18_13_6_9_1_4280 13 24
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 225 3 4 8 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 24 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 225 (Polychromatic418967fa.accept_13_10_11_4_1_2248 10 24 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 225 3 3 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 225 (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 24 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 225
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 24 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 225 3 2 8 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 24 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 24 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 225 3 1 8 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 24 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 225 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 24 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 225)))))))))))))))))))))))) (allB_succ 23 225 (allA_succ_of_accept 22 23
  225 (accept_3_4 22 23 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 225
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 23 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 225 (accept_3_4 19 23 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  23 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 225 (accept_3_4 16 23
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 225
  (Polychromatic418967fa.accept_12_3_11_9_1_193 15 23 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 225 (accept_3_4 13 23 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 225 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 23 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 225
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 23 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 225 (accept_3_4 10 23 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 225 (Polychromatic418967fa.accept_19_9_4_16_1_2586 9 23 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 225 (accept_3_4 7 23 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 225
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 5 23 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 225 (accept_3_4 4 23 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  225 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 23 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 225 (accept_3_4 1 23 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 225))))))))))))))))))))))) (allB_succ 22 225 (allA_succ_of_accept 21 22 225
  (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 22 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 225 (accept_3_5 20 22 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 225 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 22 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 225 (accept_3_5 17 22 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 225 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 22 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 225 (accept_3_5 14 22 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 225 (Polychromatic418967fa.accept_18_12_4_9_1_5452 12 22 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 225 (accept_3_5 11 22 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 225 (Polychromatic418967fa.accept_20_10_2_5_1_10647 10 22
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 225
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 22 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 225 (accept_3_5 8 22 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 225 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 22 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 225 (accept_3_5 5 22 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 225 (Polychromatic418967fa.accept_19_4_3_16_1_5097 4 22 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 225 (accept_3_5 2 22 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 225)))))))))))))))))))))) (allB_succ 21
  225 (allA_succ_of_accept 20 21 225 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 21 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 21 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 225 3 6 7 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 225
  (Polychromatic418967fa.accept_11_6_10_5_1_341 17 21 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 225 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 21 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 225 3 5 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 225 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 21 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 225
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 21 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 225 3 4 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 225 (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 21 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 225 (Polychromatic418967fa.accept_13_10_8_4_1_3098 10 21
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 225 3 3 7 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 225
  (Polychromatic418967fa.accept_14_8_7_1_1_1615 8 21 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 225 (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 21 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 225 3 2 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 225 (Polychromatic418967fa.accept_19_5_2_16_1_8013 5 21 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 225
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 21 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 225 3 1 7 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 225 (Polychromatic418967fa.accept_18_2_3_9_1_1996 2 21 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 225 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 21 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 225))))))))))))))))))))) (allB_succ 20 225
  (allA_succ_of_accept 19 20 225 (accept_3_4 19 20 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 225 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 20 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 225 (accept_3_4 16 20 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 20 225 5 3 4 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 20 225 (Polychromatic418967fa.accept_16_14_4_1_1_3049 14 20 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 225 (accept_3_4 13 20 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 20 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 225 5 2 4 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 20 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 225 (Polychromatic418967fa.accept_16_8_4_1_1_2102 8 20 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 225 (accept_3_4 7 20 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 225 (Polychromatic418967fa.accept_12_6_8_9_1_553 6
  20 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 225 5 1 4 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 225 (accept_3_4 4 20
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 225
  (Polychromatic418967fa.accept_13_3_7_4_1_435 3 20 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 20 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 225 (accept_3_4 1 20 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 225)))))))))))))))))))) (allB_succ 19 225 (allA_succ_of_accept 18 19 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 225 (accept_3_5 17 19 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 225 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 19 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 225 (accept_3_5 14 19 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 225 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 19 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 225
  (Polychromatic418967fa.accept_17_12_2_4_1_11050 12 19 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 225 (accept_3_5 11 19 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 225 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 19 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 225 (accept_3_5 8 19 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 225 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 19 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 225 (accept_3_5 5 19 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 19 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 225 (accept_3_5 2 19 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 19 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 225))))))))))))))))))) (allB_succ 18 225 (allA_succ_of_accept 17
  18 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 18 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 225 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 18 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 225 3 5 6 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 225 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  18 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 225
  (Polychromatic418967fa.accept_10_3_8_5_1_606 13 18 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 225 3 4 6 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 225 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 18 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 225 9 1 2 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 225
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 18 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 225 3 2 6 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 225 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 18 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 225
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 18 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 225 3 1 6 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 18 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 225 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 18 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 225)))))))))))))))))) (allB_succ 17 225
  (allA_succ_of_accept 16 17 225 (accept_3_4 16 17 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 225 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 17 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 225 (accept_3_4 13 17 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 225 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 17 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 225
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 17 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 225 (accept_3_4 10 17 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 225 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 17 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 225 (accept_3_4 7 17 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 225 (Polychromatic418967fa.accept_21_6_17_15_1_2833 6 17 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 225
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 17 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 225 (accept_3_4 4 17 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  225 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 17 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 225 (accept_3_4 1 17 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 225))))))))))))))))) (allB_succ 16 225 (allA_succ_of_accept 15 16 225
  (Polychromatic418967fa.accept_17_15_16_4_1_2418 15 16 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 225 (accept_3_5 14 16 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 225 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 16 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 225 (accept_3_5 11 16 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 16 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 225
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 16 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 225 (accept_3_5 8 16 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  225 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 225 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 16 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 225 (accept_3_5 5 16 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 16 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 225 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  16 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 225 (accept_3_5 2 16 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 225)))))))))))))))) (allB_succ 15 225
  (allA_succ_of_accept 14 15 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 15 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 225 3 4 5 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 225
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 15 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 15 225 5 2 3 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 15 225 3 3 5 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 225 (Polychromatic418967fa.accept_16_8_15_1_1_3006 8 15 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 225 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 15 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 225 3 2 5 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 225 5 1 3 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 225
  (Polychromatic418967fa.accept_18_4_15_9_1_6882 4 15 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 15 225 3 1 5 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 15 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 225 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 15 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 225))))))))))))))) (allB_succ 14 225
  (allA_succ_of_accept 13 14 225 (accept_3_4 13 14 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  14 225 (Polychromatic418967fa.accept_19_12_14_16_1_7935 12 14 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 14 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 225 (accept_3_4 10 14 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 225 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 14 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 225
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 14 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 14 225 (accept_3_4 7 14 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14
  225 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 14 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 225 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 225 (accept_3_4 4 14 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 225 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 225 (Polychromatic418967fa.accept_19_2_14_16_1_7992
  2 14 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 225 (accept_3_4 1 14
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 225)))))))))))))) (allB_succ 13 225 (allA_succ_of_accept 12
  13 225 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 225 (accept_3_5 11 13 225 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 225 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 13 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 225 (accept_3_5 8 13 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 225 (Polychromatic418967fa.accept_10_7_3_5_1_301 7
  13 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 225
  (Polychromatic418967fa.accept_18_6_13_9_1_4218 6 13 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 225 (accept_3_5 5 13 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  225 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 225 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 13 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 225 (accept_3_5 2 13 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 225 (Polychromatic418967fa.accept_19_1_13_16_1_12024 1 13 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 225))))))))))))) (allB_succ 12 225
  (allA_succ_of_accept 11 12 225 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 12 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 12 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 225 3 3 4 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 225
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 12 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 225 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 12 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 225 3 2 4 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 225 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 225
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 12 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 12 225 3 1 4 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 12 225 (Polychromatic418967fa.accept_13_2_12_4_1_943 2 12 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 225 (Polychromatic418967fa.accept_21_1_12_15_1_2880 1 12 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 225)))))))))))) (allB_succ 11 225
  (allA_succ_of_accept 10 11 225 (accept_3_4 10 11 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  11 225 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 11 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 11 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 225 (accept_3_4 7 11 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 225 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 225
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 11 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 225 (accept_3_4 4 11 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11
  225 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 11 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 11 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 225 (accept_3_4 1 11 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 11 225))))))))))) (allB_succ 10 225 (allA_succ_of_accept 9 10 225
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 10 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 225 (accept_3_5 8 10 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  225 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 225 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 10 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 10 225 5 1 2 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 10 225 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 10 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 225
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 10 225 (accept_3_5 2 10 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10
  225 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 225)))))))))) (allB_succ 9 225 (allA_succ_of_accept 8 9 225 (Polychromatic418967fa.accept_13_8_9_4_1_1552
  8 9 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 225
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 9 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 9 225 3 2 3 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 9 225 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 9 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 225 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 9 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 225 3 1 3 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 225
  (Polychromatic418967fa.accept_16_2_9_1_1_6404 2 9 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 225 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 9 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 9 225))))))))) (allB_succ 8 225 (allA_succ_of_accept 7 8 225 (accept_3_4 7 8
  225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 225 (Polychromatic418967fa.accept_12_6_8_9_1_553
  6 8 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 225
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 225 (accept_3_4 4 8 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 225
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 8 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 225 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 8 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 225 (accept_3_4 1 8 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 225)))))))) (allB_succ 7 225 (allA_succ_of_accept 6 7 225
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 225 (accept_3_5 5 7 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 225
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 225 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 7 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 225 (accept_3_5 2 7 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 225 (Polychromatic418967fa.accept_21_1_7_15_1_4259 1 7 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 225))))))) (allB_succ 6 225 (allA_succ_of_accept 5 6 225
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 6 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 225 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 6 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 225 3 1 2 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 225 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 6 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 225
  (Polychromatic418967fa.accept_10_1_6_5_1_304 1 6 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 225)))))) (allB_succ 5 225 (allA_succ_of_accept 4 5 225 (accept_3_4 4 5 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 225 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 5 225 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 225 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 225 (accept_3_4 1 5 225
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 225))))) (allB_succ 4 225 (allA_succ_of_accept 3 4 225
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 4 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 225 (accept_3_5 2 4 225 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 225
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 225)))) (allB_succ 3 225 (allA_succ_of_accept 2 3 225 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 225
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 225
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 3 225 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 225))) (allB_succ 2 225 (allA_succ_of_accept 1 2 225 (accept_3_4 1 2 225 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 225)) (allB_two
  225))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


