-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch261_Segment000
-- name    : Polychromatic418967fa_Branch261_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:26.095152+00:00
-- url     : https://prove2.me/theorems/cb6083e0-d102-45b4-b800-87562ed5aeba
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

def Polychromatic418967fa.branch_261_segment_000 : allB 100 261 :=
  allB_succ 99 261 (allA_succ_of_accept 98 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 97 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 261 3 32 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 95 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 261 3 31 33 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 261
  (Polychromatic418967fa.accept_10_2_9_1_1_185 92 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 91 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 261 9 10 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 89
  99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 261
  (Polychromatic418967fa.accept_10_8_9_1_1_189 88 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 261 3 29 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 85 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 261 3 28 33 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 261 9 9 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 80 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 79 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 261 3 26 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 261 3 25 33 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 73 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 261 9 8 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 71 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 261 3 23 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 68 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 67 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 261 3 22 33 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 261 (Polychromatic418967fa.accept_13_12_8_1_1_825 64 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 261 9 7 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 61 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 261 3 20 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 261 3 19 33 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 261
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 56 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 261 9 6 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 261 3 17 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 261 3 16 33 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 261 9 5 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 261 (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 261 3 14 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 261 (Polychromatic418967fa.accept_16_8_3_5_1_5512 40 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 261 3 13 33 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 261 9 4 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 261 3 11 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 261 3 10 33 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 261 9 3 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 261 3 8 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 261 3 7 33 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 261 9 2 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 261
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 261 3 5 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 261 3 4 33 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 261 9 1 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 261 3 2 33 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 261 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 99 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 261 3 1 33 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 99 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  261 (allA_succ_of_accept 97 98 261 (accept_3_4 97 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 261 (Polychromatic418967fa.accept_17_11_13_6_1_2625 96 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 261 (accept_3_4 94 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 93 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 261
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 92 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 261 (accept_3_4 91 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 90 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 261 (accept_3_4 88 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 261
  (Polychromatic418967fa.accept_11_9_10_8_1_444 86 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 261 (accept_3_4 85 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 261 (Polychromatic418967fa.accept_13_6_7_1_1_335 84 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 261 (accept_3_4 82 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 261 (Polychromatic418967fa.accept_13_3_7_1_1_334 81 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 261
  (Polychromatic418967fa.accept_21_17_14_9_1_8456 80 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 261 (accept_3_4 79 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 261 (accept_3_4 76 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 261
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 74 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 261 (accept_3_4 73 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 261 (Polychromatic418967fa.accept_23_3_6_8_1_15934 72 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 261 (accept_3_4 70 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 261
  (Polychromatic418967fa.accept_13_3_7_1_1_334 68 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 261 (accept_3_4 67 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 261 (accept_3_4 64 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 261
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 62 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 261 (accept_3_4 61 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 261 (Polychromatic418967fa.accept_13_8_7_1_1_1385 60 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 261 (accept_3_4 58 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 261 (Polychromatic418967fa.accept_18_3_8_9_1_1956 57 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 261
  (Polychromatic418967fa.accept_19_18_3_14_1_5001 56 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 261 (accept_3_4 55 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 261 (accept_3_4 52 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 261
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 50 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 261 (accept_3_4 49 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 261 (Polychromatic418967fa.accept_20_8_18_1_1_15933 48 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 261 (accept_3_4 46 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 261 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 261
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 44 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 261 (accept_3_4 43 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 261 (accept_3_4 40 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 261
  (Polychromatic418967fa.accept_21_17_14_9_1_8456 38 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 261 (accept_3_4 37 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 261 (Polychromatic418967fa.accept_17_2_13_6_1_3772 36 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 261 (accept_3_4 34 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 261
  (Polychromatic418967fa.accept_13_6_7_1_1_335 32 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 261 (accept_3_4 31 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 261 (accept_3_4 28 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 261
  (Polychromatic418967fa.accept_19_7_3_14_1_5023 26 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 261 (accept_3_4 25 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 261 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 261 (accept_3_4 22 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 261 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 261
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 261 (accept_3_4 19 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 261 (accept_3_4 16 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 261
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 261 (accept_3_4 13 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 261 (Polychromatic418967fa.accept_23_12_6_8_1_15932 12 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 261 (accept_3_4 10 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 98 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 261
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 261 (accept_3_4 7 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  261 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 261 (accept_3_4 4 98 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 261 (Polychromatic418967fa.accept_15_2_8_6_1_1340 2
  98 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 261 (accept_3_4 1 98 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  261 (allA_succ_of_accept 96 97 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 96 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 261 (accept_3_5 95 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 261
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 93 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 97 261 (accept_3_5 92 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  97 261 (Polychromatic418967fa.accept_15_1_7_6_1_6127 91 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 97 261 (Polychromatic418967fa.accept_20_10_17_1_1_8852 90 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 261 (accept_3_5 89 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 87 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 97 261 (accept_3_5 86 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  97 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 85 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 97 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 261 (accept_3_5 83 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 261 (accept_3_5 80 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 261 (Polychromatic418967fa.accept_16_15_1_5_1_2265 79 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 261 (accept_3_5 77 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 75 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 261 (accept_3_5 74 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 261 (Polychromatic418967fa.accept_13_7_6_1_1_368 72 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 261 (accept_3_5 71 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 261
  (Polychromatic418967fa.accept_17_1_12_6_1_3735 69 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 261 (accept_3_5 68 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 261 (accept_3_5 65 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 261 (accept_3_5 62 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 61 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 261 (accept_3_5 59 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 261 (accept_3_5 56 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 261 (Polychromatic418967fa.accept_13_3_6_1_1_3797 55 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 261 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 261 (accept_3_5 53 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 51 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 261 (accept_3_5 50 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 261 (Polychromatic418967fa.accept_21_7_13_9_1_6937 49 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 48 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 261 (accept_3_5 47 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 261 (accept_3_5 44 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 261 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 261 (accept_3_5 41 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 261 (accept_3_5 38 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 261 (Polychromatic418967fa.accept_21_16_13_9_1_2539 37 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 261 (accept_3_5 35 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 261
  (Polychromatic418967fa.accept_13_7_6_1_1_368 33 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 261 (accept_3_5 32 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 261 (Polychromatic418967fa.accept_20_10_17_1_1_8852 30 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 261 (accept_3_5 29 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 261 (accept_3_5 26 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 261 (accept_3_5 23 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 261
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 261 (accept_3_5 20 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 261 (Polychromatic418967fa.accept_17_2_12_6_1_3737 19 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 261 (accept_3_5 17 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 261 (accept_3_5 14 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 261 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 261 (accept_3_5 11 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 261
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 261 (accept_3_5 8 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  261 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 97 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 97 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 261 (accept_3_5 5 97 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 97
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 261 (accept_3_5 2 97 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 97
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 261
  (allA_succ_of_accept 95 96 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 94 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 96 261 3 31 32 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 96 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 92 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 96 261 (Polychromatic418967fa.accept_14_7_12_9_1_2926 91 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 261 3 30 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 261 (Polychromatic418967fa.accept_17_4_11_6_1_3730
  89 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 88 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 96 261 3 29 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 96 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 86 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 85 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 261 3 28 32 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 261
  (Polychromatic418967fa.accept_21_20_12_9_1_11514 83 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 96 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 82 96 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 261 3 27 32 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 80 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 96 261 (Polychromatic418967fa.accept_18_7_6_9_1_4205 79 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 261 3 26 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 261 (Polychromatic418967fa.accept_10_7_6_1_1_486 77
  96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 261
  (Polychromatic418967fa.accept_21_13_12_9_1_5323 76 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 96 261 3 25 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 96 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 261 3 24 32 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 261
  (Polychromatic418967fa.accept_13_6_5_1_1_834 71 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 261 (Polychromatic418967fa.accept_19_13_1_14_1_3634 70 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 96 261 3 23 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 96 261 (Polychromatic418967fa.accept_13_3_5_1_1_2144
  68 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 261 3 22 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 65 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 261 (Polychromatic418967fa.accept_13_12_5_1_1_1383 64 96
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 261 3 21 32 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382 61 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 261 3 20 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 59
  96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 261
  (Polychromatic418967fa.accept_13_6_5_1_1_834 58 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 96 261 3 19 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 96 261 (Polychromatic418967fa.accept_13_4_5_1_1_833 56 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 261 3 18 32 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 96 261 3 17 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 96 261 (Polychromatic418967fa.accept_18_14_6_9_1_1950
  50 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 261
  (Polychromatic418967fa.accept_14_7_12_9_1_2926 49 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 261 3 16 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 261 (Polychromatic418967fa.accept_10_7_6_1_1_486 47 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 261 3 15 32 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 261
  (Polychromatic418967fa.accept_18_8_6_9_1_5576 44 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 261 (Polychromatic418967fa.accept_13_4_5_1_1_833 43 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 261 3 14 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 261
  (Polychromatic418967fa.accept_21_20_12_9_1_11514 41 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 96 261 (Polychromatic418967fa.accept_19_2_1_14_1_3663 40 96 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 261 3 13 32 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 261 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 261 3 12 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 35
  96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 261
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 34 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 96 261 3 11 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 96 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 261 3 10 32 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 261
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 261 (Polychromatic418967fa.accept_19_9_1_14_1_1372 28 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 261 3 9 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 261 (Polychromatic418967fa.accept_18_8_6_9_1_5576 26 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 261 3 8 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 261 (Polychromatic418967fa.accept_21_2_12_9_1_5324 23 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 261 3 7 32 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 261
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 20 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 261 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 261 3 6 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 261
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 96 261 3 5 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 96 261 (Polychromatic418967fa.accept_18_14_6_9_1_1950 14 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 261 (Polychromatic418967fa.accept_17_13_11_6_1_4837 13 96
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 261 3 4 32 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 261 3 3 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 261
  (Polychromatic418967fa.accept_10_7_6_1_1_486 7 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 261 3 2 32 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 96 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 261 3 1 32 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 96 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 261 (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 96 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 261
  (allA_succ_of_accept 94 95 261 (accept_3_4 94 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 261 (Polychromatic418967fa.accept_15_3_5_6_1_4005 93 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 261 (accept_3_4 91 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 261 (accept_3_4 88 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 87 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 261 (accept_3_4 85 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 84 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 261 (accept_3_4 82 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 81 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 261 (accept_3_4 79 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 261
  (Polychromatic418967fa.accept_24_5_23_21_1_15917 77 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 95 261 (accept_3_4 76 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 95 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 95 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 261 (accept_3_4 73 95 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 261 (Polychromatic418967fa.accept_14_2_11_9_1_2925
  72 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 261
  (Polychromatic418967fa.accept_15_11_5_6_1_669 71 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 261 (accept_3_4 70 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 261 (accept_3_4 67 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 261
  (Polychromatic418967fa.accept_16_1_15_5_1_708 65 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 261 (accept_3_4 64 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 261 (accept_3_4 61 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 261 (Polychromatic418967fa.accept_21_18_11_9_1_6956 60 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 261 (accept_3_4 58 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 261 (Polychromatic418967fa.accept_13_5_4_1_1_364 57 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 261 (accept_3_4 55 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 261
  (Polychromatic418967fa.accept_24_5_23_21_1_15917 53 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 95 261 (accept_3_4 52 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 95 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 95 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 261 (accept_3_4 49 95 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 48
  95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 261 (accept_3_4 46 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 261 (Polychromatic418967fa.accept_20_5_15_1_1_7278 45 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 261 (accept_3_4 43 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 261 (accept_3_4 40 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 261 (accept_3_4 37 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 261
  (Polychromatic418967fa.accept_22_13_7_19_1_15931 35 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 95 261 (accept_3_4 34 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 95 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 95 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 261 (accept_3_4 31 95 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 261 (accept_3_4 28 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 261 (accept_3_4 25 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 261
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 261 (accept_3_4 22 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 261 (Polychromatic418967fa.accept_17_4_10_6_1_4869 21 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 261 (accept_3_4 19 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 261
  (Polychromatic418967fa.accept_16_1_15_5_1_708 17 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 261 (accept_3_4 16 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 261 (accept_3_4 13 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 261
  (Polychromatic418967fa.accept_15_11_5_6_1_669 11 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 261 (accept_3_4 10 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 261 (accept_3_4 7 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 261 (accept_3_4 4 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  261 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 95 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 95 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 261 (accept_3_4 1 95 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 95
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 261
  (allA_succ_of_accept 93 94 261 (Polychromatic418967fa.accept_13_2_3_1_1_3823 93 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 261 (accept_3_5 92 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 90
  94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 261 (accept_3_5 89 94
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 261
  (Polychromatic418967fa.accept_15_13_4_6_1_3046 88 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 261 (accept_3_5 86 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 261 (Polychromatic418967fa.accept_13_6_3_1_1_1413
  84 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 261 (accept_3_5 83
  94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 82 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 94 261 (Polychromatic418967fa.accept_21_18_10_9_1_5297 81 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 94 261 (accept_3_5 80 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 94 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 78
  94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 261 (accept_3_5 77 94
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 76 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 261 (accept_3_5 74 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 94 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 261 (Polychromatic418967fa.accept_13_7_3_1_1_814
  72 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 261 (accept_3_5 71
  94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 261
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 70 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 94 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 261 (accept_3_5 68 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 261 (Polychromatic418967fa.accept_12_6_10_9_1_531
  66 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 261 (accept_3_5 65
  94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 64 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 261 (accept_3_5 62 94 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 94 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 261
  (Polychromatic418967fa.accept_19_3_18_14_1_5020 60 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 94 261 (accept_3_5 59 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  94 261 (Polychromatic418967fa.accept_11_3_6_8_1_1924 58 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 94 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 261 (accept_3_5 56 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 54 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 94 261 (accept_3_5 53 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  94 261 (Polychromatic418967fa.accept_22_8_6_19_1_8133 52 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 261 (accept_3_5 50 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 261 (accept_3_5 47 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 261 (Polychromatic418967fa.accept_13_7_3_1_1_814 46 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 261 (accept_3_5 44 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 261 (accept_3_5 41 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 261 (accept_3_5 38 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 261 (accept_3_5 35 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 261 (accept_3_5 32 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 261 (accept_3_5 29 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 261 (Polychromatic418967fa.accept_13_2_3_1_1_3823 28 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 261 (accept_3_5 26 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 261
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 261 (accept_3_5 23 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 261 (Polychromatic418967fa.accept_31_21_1_13_1_15930 21 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 261 (accept_3_5 20 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 261 (accept_3_5 17 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 261 (Polychromatic418967fa.accept_17_16_9_6_1_3723 16 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 261 (accept_3_5 14 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 261 (accept_3_5 11 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 261 (Polychromatic418967fa.accept_15_10_4_6_1_2129 10 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 261 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 261 (accept_3_5 8 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 261 (accept_3_5 5 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  261 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 94 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 261 (accept_3_5 2 94 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 261
  (allA_succ_of_accept 92 93 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 92 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 91 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 261 3 30 31 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 261
  (Polychromatic418967fa.accept_16_9_13_5_1_2238 89 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316 88 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 261 3 29 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 261 (Polychromatic418967fa.accept_15_11_3_6_1_1306
  86 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 261
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 85 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 261 3 28 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 261 (Polychromatic418967fa.accept_17_15_8_6_1_8733 83 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 82 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 261 3 27 31 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 261
  (Polychromatic418967fa.accept_11_3_5_8_1_458 80 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 79 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 261 3 26 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 261 (Polychromatic418967fa.accept_13_12_2_1_1_2909
  77 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 261
  (Polychromatic418967fa.accept_15_1_3_6_1_621 76 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 261 3 25 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 261 (Polychromatic418967fa.accept_13_9_2_1_1_813 74 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 261 (Polychromatic418967fa.accept_16_9_13_5_1_2238 73 93
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 261 3 24 31 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 261
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 71 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 261 (Polychromatic418967fa.accept_15_10_3_6_1_3042 70 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 261 3 23 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  68 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 261
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 67 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 261 3 22 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 261 (Polychromatic418967fa.accept_15_5_3_6_1_2128 65 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 261 (Polychromatic418967fa.accept_13_12_2_1_1_2909 64 93
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 261 3 21 31 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 261
  (Polychromatic418967fa.accept_10_2_3_1_1_481 62 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 261 (Polychromatic418967fa.accept_13_9_2_1_1_813 61 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 261 3 20 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 261 (Polychromatic418967fa.accept_19_2_17_14_1_6399
  59 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 261
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 58 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 261 3 19 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 261 (Polychromatic418967fa.accept_15_11_3_6_1_1306 56 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 261 (Polychromatic418967fa.accept_13_3_2_1_1_2907 55 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 261 3 18 31 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 261
  (Polychromatic418967fa.accept_19_15_17_14_1_1370 53 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 93 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 52 93 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 261 3 17 31 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 261
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 50 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 261 (Polychromatic418967fa.accept_16_1_13_5_1_2280 49 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 93 261 3 16 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 93 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 47
  93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 261
  (Polychromatic418967fa.accept_11_2_5_8_1_470 46 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 93 261 3 15 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 93 261 (Polychromatic418967fa.accept_18_8_3_9_1_4232 44 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 261 (Polychromatic418967fa.accept_17_9_8_6_1_6050 43 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 261 3 14 31 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 261
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 41 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 261 (Polychromatic418967fa.accept_15_10_3_6_1_3042 40 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 261 3 13 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  38 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 261
  (Polychromatic418967fa.accept_18_1_3_9_1_328 37 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 93 261 3 12 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 93 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 261 (Polychromatic418967fa.accept_16_2_13_5_1_2257 34 93
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 261 3 11 31 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 261
  (Polychromatic418967fa.accept_10_2_3_1_1_481 32 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 261 (Polychromatic418967fa.accept_15_1_3_6_1_621 31 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 261 3 10 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 261 (Polychromatic418967fa.accept_13_3_2_1_1_2907
  29 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 261
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 93 261 3 9 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 93 261 (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 261 3 8 31 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 261
  (Polychromatic418967fa.accept_20_3_13_1_1_8886 23 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 22 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 261 3 7 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 261 (Polychromatic418967fa.accept_15_5_3_6_1_2128 20 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 261
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 93 261 3 6 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 93 261 (Polychromatic418967fa.accept_16_1_13_5_1_2280 17 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 261 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 261 3 5 31 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 261
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 261 3 4 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 261 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 261
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 93 261 3 3 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 93 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 261 (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 261 3 2 31 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 261
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 261 (Polychromatic418967fa.accept_23_4_1_8_1_15929 4 93 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 261 3 1 31 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 93 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 261
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 93 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 92 261 (allA_succ_of_accept 91 92 261 (accept_3_4 91 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 92 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 92 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 261 (accept_3_4 88 92 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 87
  92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 86 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 261 (accept_3_4 85 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 84 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 261 (accept_3_4 82 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 261 (accept_3_4 79 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 78 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 261 (accept_3_4 76 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 261 (Polychromatic418967fa.accept_18_3_2_9_1_1013 75 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 261
  (Polychromatic418967fa.accept_16_10_12_5_1_2254 74 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 261 (accept_3_4 73 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 261 (Polychromatic418967fa.accept_15_12_2_6_1_2127 72 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 261 (accept_3_4 70 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 261
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 68 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 261 (accept_3_4 67 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 261 (accept_3_4 64 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 261 (accept_3_4 61 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 261 (Polychromatic418967fa.accept_18_6_2_9_1_3056 60 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 261 (accept_3_4 58 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 261 (accept_3_4 55 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 261 (accept_3_4 52 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 261
  (Polychromatic418967fa.accept_17_16_7_6_1_7343 50 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 261 (accept_3_4 49 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 261 (accept_3_4 46 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 261
  (Polychromatic418967fa.accept_25_19_17_11_1_15928 44 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 92 261 (accept_3_4 43 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 92 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 92 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 261 (accept_3_4 40 92 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 261 (Polychromatic418967fa.accept_10_9_2_1_1_840
  39 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 261 (accept_3_4 37 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 261 (accept_3_4 34 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 261
  (Polychromatic418967fa.accept_19_13_16_14_1_3517 32 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 92 261 (accept_3_4 31 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 92 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 92 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 261 (accept_3_4 28 92 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 27
  92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 261 (accept_3_4 25 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 261 (accept_3_4 22 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 261 (Polychromatic418967fa.accept_18_3_2_9_1_1013 21 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 261 (accept_3_4 19 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 261 (accept_3_4 16 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 261 (Polychromatic418967fa.accept_14_1_8_9_1_1312 15 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 261
  (Polychromatic418967fa.accept_17_14_7_6_1_11222 14 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 261 (accept_3_4 13 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 261 (accept_3_4 10 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 92 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 261
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 261 (accept_3_4 7 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  261 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 261 (accept_3_4 4 92 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 92 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 261 (Polychromatic418967fa.accept_19_2_16_14_1_3551
  2 92 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 261 (accept_3_4 1 92
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 261
  (allA_succ_of_accept 90 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 261 (accept_3_5 89 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  87 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 261 (accept_3_5 86
  91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 261
  (Polychromatic418967fa.accept_15_10_1_6_1_3033 85 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 261 (Polychromatic418967fa.accept_15_9_1_6_1_657 84 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 261 (accept_3_5 83 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 261 (Polychromatic418967fa.accept_21_18_7_9_1_2529
  81 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 261 (accept_3_5 80
  91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 261
  (Polychromatic418967fa.accept_21_16_7_9_1_6877 79 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 261 (accept_3_5 77 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 91 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  75 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 261 (accept_3_5 74
  91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 261
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 73 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 91 261 (Polychromatic418967fa.accept_11_6_3_8_1_843 72 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 261 (accept_3_5 71 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 261 (Polychromatic418967fa.accept_15_9_1_6_1_657
  69 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 261 (accept_3_5 68
  91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 261
  (Polychromatic418967fa.accept_15_7_1_6_1_6150 67 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 261 (accept_3_5 65 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 91 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  63 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 261 (accept_3_5 62
  91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 261
  (Polychromatic418967fa.accept_11_6_3_8_1_843 61 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 91 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 261 (accept_3_5 59 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 261 (Polychromatic418967fa.accept_16_9_11_5_1_2279
  57 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 261 (accept_3_5 56
  91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 261
  (Polychromatic418967fa.accept_15_10_1_6_1_3033 55 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 261 (accept_3_5 53 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 91 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  51 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 261 (accept_3_5 50
  91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 261
  (Polychromatic418967fa.accept_11_5_3_8_1_454 49 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 91 261 (Polychromatic418967fa.accept_15_3_1_6_1_206 48 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 261 (accept_3_5 47 91 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 261
  (Polychromatic418967fa.accept_19_7_15_14_1_3659 45 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 261 (accept_3_5 44 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 261 (Polychromatic418967fa.accept_25_18_16_11_1_15927 43 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 261 (accept_3_5 41 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 261
  (Polychromatic418967fa.accept_11_6_3_8_1_843 39 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 261 (accept_3_5 38 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 261 (Polychromatic418967fa.accept_15_7_1_6_1_6150 37 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 261 (Polychromatic418967fa.accept_19_17_15_14_1_3623 36 91 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 261 (accept_3_5 35 91 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 261
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 261 (accept_3_5 32 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 261 (Polychromatic418967fa.accept_21_10_7_9_1_11527 31 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 261 (accept_3_5 29 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 261
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 261 (accept_3_5 26 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 261 (Polychromatic418967fa.accept_15_10_1_6_1_3033 25 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 261 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 261 (accept_3_5 23 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 261
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 21 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 261 (accept_3_5 20 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 261 (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 261 (accept_3_5 17 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 261
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 261 (accept_3_5 14 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 261 (Polychromatic418967fa.accept_19_13_15_14_1_3549 13 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 261 (Polychromatic418967fa.accept_14_12_7_9_1_726 12 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 261 (accept_3_5 11 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 261
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 261 (accept_3_5 8 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  261 (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 261 (accept_3_5 5 91 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 261
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 261 (accept_3_5 2 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  261 (Polychromatic418967fa.accept_19_1_15_14_1_5032 1 91 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 261
  (allA_succ_of_accept 89 90 261 (Polychromatic418967fa.accept_13_11_12_1_1_2154 89 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 88 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 261 3 29 30 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 86 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 90 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 85 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 261 3 28 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 83
  90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 261
  (Polychromatic418967fa.accept_11_5_2_8_1_866 82 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 90 261 9 9 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 90 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 261 3 26 30 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 261
  (Polychromatic418967fa.accept_16_13_10_5_1_2278 77 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 261 3 25 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 74
  90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 73 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 261 9 8 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 70 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 90 261 3 23 30 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 261 3 22 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 261 (Polychromatic418967fa.accept_20_5_10_1_1_11750
  65 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 64 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 90 261 9 7 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 90 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 261 (Polychromatic418967fa.accept_16_13_10_5_1_2278 61 90
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 261 3 20 30 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 261 3 19 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  56 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 261 9 6 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 90 261 3 17 30 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 90 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 261 3 16 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 46 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 261 9 5 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 261 3 14 30 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 261
  (Polychromatic418967fa.accept_13_2_12_1_1_343 41 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 261 3 13 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 261
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 37 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 261 9 4 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 261 3 11 30 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 261 3 10 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 261 9 3 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 261 3 8 30 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 261 3 7 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 261 9 2 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 261 3 5 30 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 261 (Polychromatic418967fa.accept_16_13_10_5_1_2278 13 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 261 3 4 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 10 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 261 9 1 10 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 261 3 2 30 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 261
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 90 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 261 3 1 30 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 90 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 90 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 261 (allA_succ_of_accept 88 89 261 (accept_3_4 88 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 89 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 89 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 261 (accept_3_4 85 89 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 84
  89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 261
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 83 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 261 (accept_3_4 82 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 261 (accept_3_4 79 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 78 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 261
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 77 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 261 (accept_3_4 76 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 75 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 261 (accept_3_4 73 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 261
  (Polychromatic418967fa.accept_25_21_14_11_1_15926 71 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 89 261 (accept_3_4 70 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 89 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004 69 89 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 261 (accept_3_4 67 89 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 66
  89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 261 (accept_3_4 64 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 261 (accept_3_4 61 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 261 (accept_3_4 58 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 261 (Polychromatic418967fa.accept_21_15_5_9_1_5315 57 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 261 (accept_3_4 55 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004 54 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 261 (accept_3_4 52 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 261 (accept_3_4 49 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 261
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 261 (accept_3_4 46 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 261 (accept_3_4 43 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 261
  (Polychromatic418967fa.accept_25_16_14_11_1_15925 41 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 89 261 (accept_3_4 40 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 89 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 89 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 89 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 261 (accept_3_4 37 89 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 36
  89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 261 (accept_3_4 34 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 261 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 261 (accept_3_4 31 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 261 (Polychromatic418967fa.accept_16_14_9_5_1_4388 30 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 261
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 261 (accept_3_4 28 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 261 (accept_3_4 25 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 261
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 261 (accept_3_4 22 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 261 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 261 (accept_3_4 19 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 261 (accept_3_4 16 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 261 (accept_3_4 13 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 261 (accept_3_4 10 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 261 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 261 (accept_3_4 7 89 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 261 (Polychromatic418967fa.accept_30_6_29_21_1_3029 6 89 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 261 (accept_3_4 4 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  261 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 89 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 261 (accept_3_4 1 89 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 261 (allA_succ_of_accept 87 88 261 (Polychromatic418967fa.accept_13_9_10_1_1_1389 87 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 261 (accept_3_5 86 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 261
  (Polychromatic418967fa.accept_16_4_8_5_1_3317 84 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 88 261 (accept_3_5 83 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  88 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 82 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 88 261 (Polychromatic418967fa.accept_21_18_4_9_1_8484 81 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 261 (accept_3_5 80 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 78 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 261 (accept_3_5 77 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 261 (accept_3_5 74 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 261
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 261 (accept_3_5 71 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 261 (Polychromatic418967fa.accept_19_13_12_14_1_9217 70 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 261 (accept_3_5 68 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 66 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 261 (accept_3_5 65 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 261 (Polychromatic418967fa.accept_15_4_13_6_1_642 64 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 261 (accept_3_5 62 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 261
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 60 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 261 (accept_3_5 59 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 261 (Polychromatic418967fa.accept_14_2_4_9_1_2121 58 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 261 (Polychromatic418967fa.accept_21_15_4_9_1_5340 57 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 261 (accept_3_5 56 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 261 (accept_3_5 53 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 261 (Polychromatic418967fa.accept_15_7_13_6_1_696 52 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 261 (Polychromatic418967fa.accept_16_3_8_5_1_6790 51 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 261 (accept_3_5 50 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 261 (accept_3_5 47 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 261 (Polychromatic418967fa.accept_24_22_16_21_1_10916 46 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 261 (Polychromatic418967fa.accept_16_13_8_5_1_3298 45 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 261 (accept_3_5 44 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 261 (accept_3_5 41 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 261 (accept_3_5 38 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 261
  (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 261 (accept_3_5 35 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 261 (accept_3_5 32 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 261 (accept_3_5 29 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 261 (Polychromatic418967fa.accept_16_12_8_5_1_3316 28 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 261 (accept_3_5 26 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 261
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 261 (accept_3_5 23 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 261 (Polychromatic418967fa.accept_13_9_10_1_1_1389 22 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 261 (Polychromatic418967fa.accept_19_2_12_14_1_11919 21 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 261 (accept_3_5 20 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 261 (accept_3_5 17 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 261 (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 261 (Polychromatic418967fa.accept_18_15_16_9_1_4299 15 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 261 (accept_3_5 14 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 261 (accept_3_5 11 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 261 (Polychromatic418967fa.accept_19_10_12_14_1_3613 10 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 261 (accept_3_5 8 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 261 (accept_3_5 5 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  261 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 88 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 261 (accept_3_5 2 88 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 261
  (allA_succ_of_accept 86 87 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 85 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 261 3 28 29 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 261 3 27 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 261 (Polychromatic418967fa.accept_13_2_9_1_1_67 80
  87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 79 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 261 3 26 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 261 3 25 29 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 261 3 24 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 71
  87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 261 3 23 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 67 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 261 3 22 29 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 65 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 261 3 21 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 261 3 20 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 87 261 29 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 87 261 3 19 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 87 261 3 18 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 87 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 53 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 261 (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 87
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 87 261 3 17 29 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 87 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 261 3 16 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 47
  87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 87 261 3 15 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 87 261 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 261 3 14 29 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 261 3 13 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 87 261 3 12 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 87 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 261 3 11 29 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 261
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 32 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 261 3 10 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 29 87 261 29 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 28 87 261 (Polychromatic418967fa.accept_13_2_9_1_1_67 28
  87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 261 3 9 29 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 261 3 8 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 261 3 7 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 261 3 6 29 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 261 3 5 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 261 3 4 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 261 3 3 29 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 261 3 2 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 261
  (Polychromatic418967fa.accept_10_4_7_1_1_471 4 87 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 261 3 1 29 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 87 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 261
  (allA_succ_of_accept 85 86 261 (accept_3_4 85 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 261 (Polychromatic418967fa.accept_13_6_8_1_1_2913 84 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 261 (accept_3_4 82 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 261 (Polychromatic418967fa.accept_14_11_2_9_1_5873 81 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 261
  (Polychromatic418967fa.accept_15_5_11_6_1_692 80 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 261 (accept_3_4 79 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 261 (accept_3_4 76 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 261
  (Polychromatic418967fa.accept_13_9_8_1_1_824 74 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 261 (accept_3_4 73 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 261 (accept_3_4 70 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 69 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 261
  (Polychromatic418967fa.accept_16_4_6_5_1_2245 68 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 261 (accept_3_4 67 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 261 (accept_3_4 64 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 261 (accept_3_4 61 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 261 (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 261 (accept_3_4 58 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 261 (Polychromatic418967fa.accept_10_7_6_1_1_486 57 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 261
  (Polychromatic418967fa.accept_17_5_1_6_1_2615 56 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 261 (accept_3_4 55 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 261 (accept_3_4 52 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 261
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 50 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 261 (accept_3_4 49 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 261 (Polychromatic418967fa.accept_13_9_8_1_1_824 48 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 261 (accept_3_4 46 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 261
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 261 (accept_3_4 43 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 261 (accept_3_4 40 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 261
  (Polychromatic418967fa.accept_13_12_8_1_1_825 38 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 261 (accept_3_4 37 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 261 (Polychromatic418967fa.accept_16_4_6_5_1_2245 36 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 261 (accept_3_4 34 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 261 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 261 (accept_3_4 31 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 261 (accept_3_4 28 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 261
  (Polychromatic418967fa.accept_19_7_10_14_1_3599 26 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 261 (accept_3_4 25 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 261 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 261 (accept_3_4 22 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 261
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 261 (accept_3_4 19 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 261 (accept_3_4 16 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 261
  (Polychromatic418967fa.accept_20_14_6_1_1_3023 14 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 261 (accept_3_4 13 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 261 (accept_3_4 10 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 261 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 86 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 261
  (Polychromatic418967fa.accept_22_8_20_19_1_8153 8 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 261 (accept_3_4 7 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  261 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 261 (accept_3_4 4 86 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  86 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 261 (accept_3_4 1 86 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 261
  (allA_succ_of_accept 84 85 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 84 85 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 261 (accept_3_5 83 85 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 261 (Polychromatic418967fa.accept_13_3_7_1_1_334
  81 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 261 (accept_3_5 80
  85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 79 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 261 (Polychromatic418967fa.accept_14_8_1_9_1_2085 78 85 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 261 (accept_3_5 77 85 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 261 (Polychromatic418967fa.accept_12_3_1_9_1_202
  75 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 261 (accept_3_5 74
  85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 261 (Polychromatic418967fa.accept_15_12_10_6_1_2134 72 85 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 261 (accept_3_5 71 85 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 69
  85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 261 (accept_3_5 68 85
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 261
  (Polychromatic418967fa.accept_23_21_16_8_1_15924 67 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 85 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 261 (accept_3_5 65 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 261 (accept_3_5 62 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 261 (Polychromatic418967fa.accept_15_1_10_6_1_631 61 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 85 261 (Polychromatic418967fa.accept_13_8_7_1_1_1385 60 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 261 (accept_3_5 59 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 261
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 57 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 261 (accept_3_5 56 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 261 (accept_3_5 53 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 51 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 261 (accept_3_5 50 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 261 (accept_3_5 47 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 261 (accept_3_5 44 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 261 (Polychromatic418967fa.accept_19_5_9_14_1_3505 43 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 261 (Polychromatic418967fa.accept_13_3_7_1_1_334 42 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 261 (accept_3_5 41 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 261 (accept_3_5 38 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 261 (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 261 (accept_3_5 35 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 261
  (Polychromatic418967fa.accept_15_3_10_6_1_632 33 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 261 (accept_3_5 32 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 261 (Polychromatic418967fa.accept_19_11_9_14_1_6386 30 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 261 (accept_3_5 29 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 261 (accept_3_5 26 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 261 (Polychromatic418967fa.accept_19_6_9_14_1_3541 25 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 261 (accept_3_5 23 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 261
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 261 (accept_3_5 20 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 261 (Polychromatic418967fa.accept_15_3_10_6_1_632 18 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 261 (accept_3_5 17 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 261 (accept_3_5 14 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 261 (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 261 (accept_3_5 11 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 85 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 261 (accept_3_5 8 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  261 (Polychromatic418967fa.accept_24_7_13_21_1_10971 7 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 85 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 261 (accept_3_5 5 85 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 261 (accept_3_5 2 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  261 (Polychromatic418967fa.accept_15_1_10_6_1_631 1 85 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 85 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 84 261 (allA_succ_of_accept 83 84 261 (Polychromatic418967fa.accept_13_5_6_1_1_822 83 84 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 261
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 82 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 84 261 3 27 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 84 261 (Polychromatic418967fa.accept_13_2_6_1_1_3807 80 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 261 (Polychromatic418967fa.accept_15_4_9_6_1_627 79 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 261 3 26 28 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 261
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 261 (Polychromatic418967fa.accept_15_1_9_6_1_1323 76 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 84 261 3 25 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 84 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902
  74 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 261
  (Polychromatic418967fa.accept_8_1_4_5_1_48 73 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 261 3 24 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 261 (Polychromatic418967fa.accept_15_11_9_6_1_1321 71 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 84 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 70 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 261 3 23 28 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 261
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 68 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 84 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 67 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 261 3 22 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 65
  84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 261
  (Polychromatic418967fa.accept_15_4_9_6_1_627 64 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 84 261 3 21 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 84 261 (Polychromatic418967fa.accept_19_5_8_14_1_6384 62 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 61 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 261 3 20 28 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 261
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 59 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 261 (Polychromatic418967fa.accept_17_7_16_6_1_3705 58 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 84 261 3 19 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 84 261 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  56 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 261
  (Polychromatic418967fa.accept_10_5_4_1_1_842 55 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 261 3 18 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 84 261 (Polychromatic418967fa.accept_18_17_12_9_1_3031 53 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 261 (Polychromatic418967fa.accept_18_16_12_9_1_5504 52 84
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 261 3 17 28 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 261
  (Polychromatic418967fa.accept_20_10_4_1_1_8840 50 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 84 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 261 3 16 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  47 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 261
  (Polychromatic418967fa.accept_13_7_6_1_1_368 46 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 84 261 3 15 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 84 261 (Polychromatic418967fa.accept_13_5_6_1_1_822 44 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 261 (Polychromatic418967fa.accept_17_9_16_6_1_4820 43 84
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 261 3 14 28 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 261
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 261 (Polychromatic418967fa.accept_16_8_4_5_1_4379 40 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 84 261 3 13 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 84 261 (Polychromatic418967fa.accept_16_6_4_5_1_2272
  38 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 261
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 261 3 12 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 34 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 261 3 11 28 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 261
  (Polychromatic418967fa.accept_19_13_8_14_1_4960 32 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 261 (Polychromatic418967fa.accept_13_5_6_1_1_822 31 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 261 3 10 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 261 (Polychromatic418967fa.accept_13_3_6_1_1_3797
  29 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 261
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 84 261 3 9 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 84 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 261 3 8 28 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 261
  (Polychromatic418967fa.accept_18_5_12_9_1_6871 23 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 22 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 261 3 7 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 261 (Polychromatic418967fa.accept_13_7_6_1_1_368 20 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 261
  (Polychromatic418967fa.accept_15_4_9_6_1_627 19 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 261 3 6 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 261 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 261 3 5 28 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 261
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 84 261 (Polychromatic418967fa.accept_19_13_8_14_1_4960 13 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 261 3 4 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 261 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 261
  (Polychromatic418967fa.accept_17_10_16_6_1_4890 10 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 84 261 3 3 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 84 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 261 3 2 28 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 261
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 84 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 261 3 1 28 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 261 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 84 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 261
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 261
  (allA_succ_of_accept 82 83 261 (accept_3_4 82 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 261 (accept_3_4 79 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 261
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 77 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 261 (accept_3_4 76 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 75 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 261 (accept_3_4 73 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 261 (accept_3_4 70 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 261 (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 261 (accept_3_4 67 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 261
  (Polychromatic418967fa.accept_17_14_15_6_1_4819 65 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 261 (accept_3_4 64 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 261 (accept_3_4 61 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 261 (accept_3_4 58 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 261 (accept_3_4 55 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 261 (accept_3_4 52 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 261 (accept_3_4 49 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 261
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 261 (accept_3_4 46 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 261 (accept_3_4 43 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 261
  (Polychromatic418967fa.accept_19_3_7_14_1_3669 41 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 261 (accept_3_4 40 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 261 (accept_3_4 37 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 261
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 261 (accept_3_4 34 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 261 (Polychromatic418967fa.accept_18_15_11_9_1_4256 33 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 261 (accept_3_4 31 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 261 (accept_3_4 28 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 261 (accept_3_4 25 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 261
  (Polychromatic418967fa.accept_19_4_7_14_1_3537 23 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 261 (accept_3_4 22 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 261 (accept_3_4 19 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 261 (accept_3_4 16 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 261 (accept_3_4 13 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 261 (accept_3_4 10 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 261 (accept_3_4 7 83 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 261
  (Polychromatic418967fa.accept_20_5_3_1_1_10415 5 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 261 (accept_3_4 4 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 83 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 261 (accept_3_4 1 83 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 261 (allA_succ_of_accept 81 82 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 261 (accept_3_5 80 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 78 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 82 261 (accept_3_5 77 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  82 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 76 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 261 (accept_3_5 74 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 82 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 261
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 72 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 261 (accept_3_5 71 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 261 (Polychromatic418967fa.accept_13_5_4_1_1_364 70 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 261 (accept_3_5 68 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 261 (accept_3_5 65 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 261 (Polychromatic418967fa.accept_19_7_6_14_1_11872 64 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 261 (accept_3_5 62 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 261 (accept_3_5 59 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 58 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 57 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 261 (accept_3_5 56 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 261 (accept_3_5 53 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 261 (accept_3_5 50 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 261
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 48 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 261 (accept_3_5 47 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 261 (accept_3_5 44 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 261 (accept_3_5 41 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 261 (Polychromatic418967fa.accept_25_15_7_11_1_15923 40 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 261 (accept_3_5 38 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 261 (accept_3_5 35 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 261 (Polychromatic418967fa.accept_22_12_16_19_1_12914 34 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 261 (accept_3_5 32 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 261 (accept_3_5 29 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 261 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 261 (accept_3_5 26 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 261 (accept_3_5 23 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 261 (Polychromatic418967fa.accept_23_22_13_8_1_15922 22 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 261 (Polychromatic418967fa.accept_14_7_12_9_1_2926 21 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 261 (accept_3_5 20 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 261 (accept_3_5 17 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 261 (accept_3_5 14 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 261
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 261 (accept_3_5 11 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 261 (accept_3_5 8 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 261 (accept_3_5 5 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  261 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 82 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 261 (accept_3_5 2 82 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 261
  (allA_succ_of_accept 80 81 261 (Polychromatic418967fa.accept_13_2_3_1_1_3823 80 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 261 (Polychromatic418967fa.accept_16_15_1_5_1_2265 79 81
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 261 3 26 27 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 261
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 77 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 261 3 25 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 261 (Polychromatic418967fa.accept_19_17_5_14_1_3587
  74 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 261
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 73 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 261 9 8 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 261 (Polychromatic418967fa.accept_13_6_3_1_1_1413 71 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 261 (Polychromatic418967fa.accept_13_5_3_1_1_1398 70 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 261 3 23 27 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 261 3 22 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 261 (Polychromatic418967fa.accept_19_8_5_14_1_3586
  65 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 261
  (Polychromatic418967fa.accept_21_1_18_9_1_5290 64 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 261 9 7 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 261 3 20 27 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 261
  (Polychromatic418967fa.accept_13_7_3_1_1_814 59 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 261 (Polychromatic418967fa.accept_13_6_3_1_1_1413 58 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 261 3 19 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  56 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 55 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 261 9 6 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 261 (Polychromatic418967fa.accept_17_2_13_6_1_3772 53 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 261 3 17 27 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 261
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 50 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 261 (Polychromatic418967fa.accept_19_11_5_14_1_6351 49 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 261 3 16 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 261
  (Polychromatic418967fa.accept_13_7_3_1_1_814 46 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 261 9 5 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 261 (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 261 3 14 27 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 261 3 13 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 261 (Polychromatic418967fa.accept_16_6_1_5_1_2242
  38 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 261
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 261 9 4 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 261 (Polychromatic418967fa.accept_19_16_5_14_1_11928 35 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 261 3 11 27 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 261
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 261 (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 261 3 10 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371
  29 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 261 9 3 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 261 (Polychromatic418967fa.accept_16_9_1_5_1_2282 25 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 261 3 8 27 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 261
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 261 (Polychromatic418967fa.accept_16_6_1_5_1_2242 22 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 261 3 7 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 261 9 2 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 261 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 261 (Polychromatic418967fa.accept_14_2_11_9_1_2925 16 81
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 261 3 5 27 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 261
  (Polychromatic418967fa.accept_21_14_18_9_1_5330 14 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 261 3 4 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 261 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 261
  (Polychromatic418967fa.accept_19_10_5_14_1_3583 10 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 261 9 1 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 261 (Polychromatic418967fa.accept_19_8_5_14_1_3586 8 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 261 3 2 27 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 81 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 261 3 1 27 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 261 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 81 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 261
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 81 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 261
  (allA_succ_of_accept 79 80 261 (accept_3_4 79 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 261 (accept_3_4 76 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 261
  (Polychromatic418967fa.accept_13_9_2_1_1_813 74 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 261 (accept_3_4 73 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 261 (Polychromatic418967fa.accept_11_6_3_8_1_843 72 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 261 (accept_3_4 70 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 261 (accept_3_4 67 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 261 (accept_3_4 64 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 261 (Polychromatic418967fa.accept_15_3_5_6_1_4005 63 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 261 (accept_3_4 61 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 261 (accept_3_4 58 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 261
  (Polychromatic418967fa.accept_15_11_5_6_1_669 56 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 261 (accept_3_4 55 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 261 (accept_3_4 52 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 261 (Polychromatic418967fa.accept_13_12_2_1_1_2909 51 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 261 (accept_3_4 49 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 261 (accept_3_4 46 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 261 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 261
  (Polychromatic418967fa.accept_15_14_5_6_1_6168 44 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 261 (accept_3_4 43 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 261 (accept_3_4 40 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 261 (Polychromatic418967fa.accept_11_6_3_8_1_843 39 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 261
  (Polychromatic418967fa.accept_11_5_3_8_1_454 38 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 261 (accept_3_4 37 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 261 (accept_3_4 34 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 261
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 261 (accept_3_4 31 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 261 (accept_3_4 28 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 261 (accept_3_4 25 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 261 (Polychromatic418967fa.accept_18_6_8_9_1_1960 24 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 261 (accept_3_4 22 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 261 (Polychromatic418967fa.accept_18_3_8_9_1_1956 21 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 261 (accept_3_4 19 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 261 (accept_3_4 16 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 261
  (Polychromatic418967fa.accept_15_14_5_6_1_6168 14 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 261 (accept_3_4 13 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 261 (accept_3_4 10 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 261 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 80 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 261 (accept_3_4 7 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  261 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 261 (accept_3_4 4 80 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 261 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 80 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 261 (Polychromatic418967fa.accept_17_2_12_6_1_3737
  2 80 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 261 (accept_3_4 1 80
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 261
  (allA_succ_of_accept 78 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 261 (accept_3_5 77 79 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 261 (Polychromatic418967fa.accept_10_5_9_1_1_187
  75 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 261 (accept_3_5 74
  79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 261
  (Polychromatic418967fa.accept_15_13_4_6_1_3046 73 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 79 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 261 (accept_3_5 71 79 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 261 (Polychromatic418967fa.accept_15_9_4_6_1_3075
  69 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 261 (accept_3_5 68
  79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 261
  (Polychromatic418967fa.accept_21_4_16_9_1_14425 67 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 261 (accept_3_5 65 79 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  63 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 261 (accept_3_5 62
  79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 261
  (Polychromatic418967fa.accept_22_17_13_19_1_11281 61 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 261 (accept_3_5 59 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 261
  (Polychromatic418967fa.accept_18_3_7_9_1_5486 57 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 261 (accept_3_5 56 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 261 (accept_3_5 53 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 261
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 261 (accept_3_5 50 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 261 (accept_3_5 47 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 261 (accept_3_5 44 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 261 (Polychromatic418967fa.accept_15_13_4_6_1_3046 43 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 261 (accept_3_5 41 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 261
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 261 (accept_3_5 38 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 261 (Polychromatic418967fa.accept_19_18_3_14_1_5001 37 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 261 (Polychromatic418967fa.accept_16_4_15_5_1_5537 36 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 261 (accept_3_5 35 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 261
  (Polychromatic418967fa.accept_16_1_15_5_1_708 33 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 261 (accept_3_5 32 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 261 (Polychromatic418967fa.accept_21_10_16_9_1_5302 31 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 261 (accept_3_5 29 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 261
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 261 (accept_3_5 26 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 261 (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 261 (accept_3_5 23 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 261
  (Polychromatic418967fa.accept_17_4_11_6_1_3730 21 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 261 (accept_3_5 20 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 261 (Polychromatic418967fa.accept_25_19_4_11_1_15921 19 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 261 (accept_3_5 17 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 261 (accept_3_5 14 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 261 (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 261 (accept_3_5 11 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 261
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 261 (accept_3_5 8 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  261 (Polychromatic418967fa.accept_19_7_3_14_1_5023 7 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 261 (accept_3_5 5 79 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 261
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 261 (accept_3_5 2 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  261 (Polychromatic418967fa.accept_16_1_15_5_1_708 1 79 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 79 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  78 261 (allA_succ_of_accept 77 78 261 (Polychromatic418967fa.accept_19_1_2_14_1_3666 77 78 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 76
  78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 261 3 25 26 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 74 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 73 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 261 3 24 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 261
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 70 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 261 3 23 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 261 3 22 26 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 261
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 65 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 64 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 261 3 21 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 62
  78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 261
  (Polychromatic418967fa.accept_15_1_3_6_1_621 61 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 261 3 20 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 261 3 19 26 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 261 3 18 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 53
  78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 261 3 17 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 261 3 16 26 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 261 3 15 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  44 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 261 3 14 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 261 3 13 26 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 261 3 12 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 261 3 11 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 261 3 10 26 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 261
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 261 3 9 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 261
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 261 3 8 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 261 3 7 26 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 261 3 6 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 261 3 5 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 261 3 4 26 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 261 3 3 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 261 3 2 26 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 261 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 78 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 261 3 1 26 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 78 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 261 (Polychromatic418967fa.accept_14_1_8_9_1_1312 1 78 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 261
  (allA_succ_of_accept 76 77 261 (accept_3_4 76 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 261 (accept_3_4 73 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 261 (Polychromatic418967fa.accept_14_2_7_9_1_2937 72 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 261
  (Polychromatic418967fa.accept_15_11_2_6_1_3010 71 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 261 (accept_3_4 70 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 261 (Polychromatic418967fa.accept_18_15_5_9_1_5529 69 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 261 (accept_3_4 67 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 66 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 261
  (Polychromatic418967fa.accept_16_1_13_5_1_2280 65 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 261 (accept_3_4 64 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 261 (accept_3_4 61 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662 60 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 261
  (Polychromatic418967fa.accept_17_8_9_6_1_7330 59 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 261 (accept_3_4 58 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 261 (Polychromatic418967fa.accept_13_5_12_1_1_2123 57 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 261 (accept_3_4 55 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 261 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 261
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 53 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 261 (accept_3_4 52 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 261 (accept_3_4 49 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 261 (Polychromatic418967fa.accept_18_12_5_9_1_6896 48 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 261
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 261 (accept_3_4 46 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 261 (Polychromatic418967fa.accept_21_3_14_9_1_5299 45 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 261 (accept_3_4 43 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 261 (Polychromatic418967fa.accept_15_12_2_6_1_2127 42 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 261
  (Polychromatic418967fa.accept_13_2_12_1_1_343 41 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 261 (accept_3_4 40 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 261 (accept_3_4 37 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 261
  (Polychromatic418967fa.accept_22_13_11_19_1_8148 35 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 77 261 (accept_3_4 34 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 77 261 (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 77 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 261 (accept_3_4 31 77 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 261 (Polychromatic418967fa.accept_14_2_7_9_1_2937
  30 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 261
  (Polychromatic418967fa.accept_19_10_1_14_1_9224 29 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 261 (accept_3_4 28 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 261 (accept_3_4 25 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 261 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 261
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 23 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 261 (accept_3_4 22 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 261 (accept_3_4 19 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 261 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 261
  (Polychromatic418967fa.accept_16_1_13_5_1_2280 17 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 261 (accept_3_4 16 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 261 (accept_3_4 13 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 261 (Polychromatic418967fa.accept_14_12_7_9_1_726 12 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 261
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 261 (accept_3_4 10 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 261 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 261 (accept_3_4 7 77 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 77 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 261
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 261 (accept_3_4 4 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  261 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 77 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 261 (accept_3_4 1 77 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 261 (allA_succ_of_accept 75 76 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 75 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 261 (accept_3_5 74 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 261 (accept_3_5 71 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 261 (Polychromatic418967fa.accept_15_10_1_6_1_3033 70 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 261 (Polychromatic418967fa.accept_15_9_1_6_1_657 69 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 261 (accept_3_5 68 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 261 (accept_3_5 65 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 261 (Polychromatic418967fa.accept_15_3_1_6_1_206 63 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 261 (accept_3_5 62 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 261 (accept_3_5 59 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 261 (Polychromatic418967fa.accept_16_10_12_5_1_2254 58 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 261 (accept_3_5 56 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 54 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 261 (accept_3_5 53 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 261 (Polychromatic418967fa.accept_13_12_11_1_1_2920 51 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 261 (accept_3_5 50 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 261
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 261 (accept_3_5 47 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 261 (accept_3_5 44 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 261 (accept_3_5 41 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 261 (Polychromatic418967fa.accept_15_10_1_6_1_3033 40 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 261 (accept_3_5 38 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 261 (accept_3_5 35 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 261 (Polychromatic418967fa.accept_13_8_11_1_1_3789 34 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 261 (accept_3_5 32 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 261 (accept_3_5 29 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 261 (Polychromatic418967fa.accept_21_7_13_9_1_6937 28 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 261 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 261 (accept_3_5 26 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 261 (accept_3_5 23 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 261 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 261 (accept_3_5 20 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 261 (accept_3_5 17 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 261 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 261 (accept_3_5 14 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 261 (accept_3_5 11 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 261 (accept_3_5 8 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 261 (accept_3_5 5 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 76 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 76 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 261 (accept_3_5 2 76 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 261 (allA_succ_of_accept
  74 75 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 75 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 261 3 24 25 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 71 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 261 3 23 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 261 (Polychromatic418967fa.accept_18_14_3_9_1_4234
  68 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 261 3 22 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 65 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 64 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 261 3 21 25 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 261 3 20 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 59
  75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 261 3 19 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 261 3 18 25 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 261 3 17 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 261 3 16 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 261 3 15 25 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 261
  (Polychromatic418967fa.accept_10_4_5_1_1_497 44 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 261 3 14 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 261
  (Polychromatic418967fa.accept_16_8_11_5_1_3319 40 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 261 3 13 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 261 3 12 25 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 261 3 11 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 261 3 10 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 261 (Polychromatic418967fa.accept_22_6_9_19_1_11352 28 75
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 261 3 9 25 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 261 3 8 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 261 3 7 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 261 (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 261 3 6 25 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 261 3 5 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 261 3 4 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 261 3 3 25 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 261
  (Polychromatic418967fa.accept_16_8_11_5_1_3319 8 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 261 3 2 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 75 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 261 3 1 25 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 75 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 261 (allA_succ_of_accept
  73 74 261 (accept_3_4 73 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 261
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 261 (accept_3_4 70 74 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 68
  74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 261 (accept_3_4 67 74
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 261
  (Polychromatic418967fa.accept_12_6_2_9_1_537 66 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 74 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 261 (accept_3_4 64 74 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 62
  74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 261 (accept_3_4 61 74
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 261
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 261 (accept_3_4 58 74 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 261
  (Polychromatic418967fa.accept_26_4_22_1_1_15920 56 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 261 (accept_3_4 55 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 261 (accept_3_4 52 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 261
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 50 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 261 (accept_3_4 49 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 261 (accept_3_4 46 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 74 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 261
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 261 (accept_3_4 43 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 261 (accept_3_4 40 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 261
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 38 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 261 (accept_3_4 37 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 261 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 261 (accept_3_4 34 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 74 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 261
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 32 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 261 (accept_3_4 31 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 261 (accept_3_4 28 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 261 (accept_3_4 25 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 261 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 261 (accept_3_4 22 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 261 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 74 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 261 (accept_3_4 19 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 261 (accept_3_4 16 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 261
  (Polychromatic418967fa.accept_16_14_10_5_1_1393 14 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 261 (accept_3_4 13 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 261 (accept_3_4 10 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 74 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 261
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 261 (accept_3_4 7 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  261 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 261 (accept_3_4 4 74 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 261 (Polychromatic418967fa.accept_13_2_9_1_1_67 2
  74 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 261 (accept_3_4 1 74 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 261 (allA_succ_of_accept
  72 73 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 261 (accept_3_5 71 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 73 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 73 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 261 (accept_3_5 68 73 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 261 (Polychromatic418967fa.accept_15_7_13_6_1_696
  67 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 261
  (Polychromatic418967fa.accept_19_9_16_14_1_11871 66 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 73 261 (accept_3_5 65 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 73 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 261 (accept_3_5 62 73 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 61
  73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 261 (accept_3_5 59 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 261 (accept_3_5 56 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 73 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 54 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 261 (accept_3_5 53 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 261 (accept_3_5 50 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 261 (Polychromatic418967fa.accept_15_4_13_6_1_642 49 73 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 261 (accept_3_5 47 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 261 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 261 (accept_3_5 44 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 73 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 261
  (Polychromatic418967fa.accept_10_2_3_1_1_481 42 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 261 (accept_3_5 41 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 261 (accept_3_5 38 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 73 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 261 (accept_3_5 35 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 261 (accept_3_5 32 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 261 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 73 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 261
  (Polychromatic418967fa.accept_16_14_9_5_1_4388 30 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 261 (accept_3_5 29 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 261 (accept_3_5 26 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 261 (Polychromatic418967fa.accept_13_12_8_1_1_825 25 73 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 261
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 261 (accept_3_5 23 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 261 (Polychromatic418967fa.accept_17_4_5_6_1_8717 21 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 261 (accept_3_5 20 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 73 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 261
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 261 (accept_3_5 17 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 261 (accept_3_5 14 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 73 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 261 (accept_3_5 11 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 261 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 261 (accept_3_5 8 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 261 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 73 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 261 (accept_3_5 5 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 73 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 261 (accept_3_5 2 73 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 73 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 261 (allA_succ_of_accept 71
  72 261 (Polychromatic418967fa.accept_13_6_7_1_1_335 71 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 261 (Polychromatic418967fa.accept_15_10_12_6_1_3000 70 72 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 261 3 23 24 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 261
  (Polychromatic418967fa.accept_13_3_7_1_1_334 68 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 261 (Polychromatic418967fa.accept_14_11_2_9_1_5873 67 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 261 3 22 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 261 (Polychromatic418967fa.accept_15_5_12_6_1_639
  65 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 261
  (Polychromatic418967fa.accept_19_7_15_14_1_3659 64 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 261 9 7 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 261 (Polychromatic418967fa.accept_15_2_12_6_1_3063 62 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 261 (Polychromatic418967fa.accept_16_13_8_5_1_3298 61 72
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 261 3 20 24 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 261
  (Polychromatic418967fa.accept_10_9_2_1_1_840 59 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 261 (Polychromatic418967fa.accept_11_3_6_8_1_1924 58 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 261 3 19 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 56
  72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 261
  (Polychromatic418967fa.accept_13_3_7_1_1_334 55 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 261 9 6 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 261 (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 72
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 261 3 17 24 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 261
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 50 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 261 3 16 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 261 (Polychromatic418967fa.accept_11_3_6_8_1_1924
  47 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 261 9 5 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 261 (Polychromatic418967fa.accept_16_12_8_5_1_3316 44 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 72 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 261 3 14 24 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 261
  (Polychromatic418967fa.accept_23_18_3_8_1_15919 41 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 261 (Polychromatic418967fa.accept_15_10_12_6_1_3000 40 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 261 3 13 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 261
  (Polychromatic418967fa.accept_30_8_12_21_1_15918 38 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 72 261 (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 72 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 261 9 4 8 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 261
  (Polychromatic418967fa.accept_14_7_2_9_1_2093 35 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 261 (Polychromatic418967fa.accept_13_8_7_1_1_1385 34 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 261 3 11 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 261 (Polychromatic418967fa.accept_13_6_7_1_1_335 32
  72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 261
  (Polychromatic418967fa.accept_20_11_12_1_1_13132 31 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 72 261 3 10 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 72 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 72 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 261
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 28 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 261 9 3 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 261 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 72 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 261 3 8 24 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 261
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 261 (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 261 3 7 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 261 (Polychromatic418967fa.accept_15_5_12_6_1_639 20 72 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 261
  (Polychromatic418967fa.accept_10_9_2_1_1_840 19 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 261 9 2 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 261 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 261 3 5 24 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 261
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 261 3 4 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 261 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 72 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 261
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 261 9 1 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 261 (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 261 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 72 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 261 3 2 24 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 261
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 261 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 72 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 261 3 1 24 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 261 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 72 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 261
  (Polychromatic418967fa.accept_19_1_15_14_1_5032 1 72 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 261
  (allA_succ_of_accept 70 71 261 (accept_3_4 70 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 261 (accept_3_4 67 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 261
  (Polychromatic418967fa.accept_15_5_11_6_1_692 65 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 261 (accept_3_4 64 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 261 (accept_3_4 61 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 71 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 261 (accept_3_4 58 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 57 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 261 (accept_3_4 55 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 261
  (Polychromatic418967fa.accept_24_5_23_21_1_15917 53 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 71 261 (accept_3_4 52 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 71 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 71 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 261 (accept_3_4 49 71 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 48
  71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 261
  (Polychromatic418967fa.accept_11_3_5_8_1_458 47 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 261 (accept_3_4 46 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 261 (accept_3_4 43 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 261 (accept_3_4 40 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 261 (accept_3_4 37 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 71 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 261
  (Polychromatic418967fa.accept_11_2_5_8_1_470 35 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 261 (accept_3_4 34 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 261 (Polychromatic418967fa.accept_13_7_6_1_1_368 33 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 261 (accept_3_4 31 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 261
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 261 (accept_3_4 28 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 261 (accept_3_4 25 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 261
  (Polychromatic418967fa.accept_25_23_21_11_1_15916 23 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 71 261 (accept_3_4 22 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 71 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 71 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 261 (accept_3_4 19 71 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 261 (accept_3_4 16 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 261 (accept_3_4 13 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 261 (Polychromatic418967fa.accept_16_12_7_5_1_1412 12 71 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 261
  (Polychromatic418967fa.accept_16_11_7_5_1_4364 11 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 261 (accept_3_4 10 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 261 (accept_3_4 7 71 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 261
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 261 (accept_3_4 4 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 71 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 261 (accept_3_4 1 71 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 261
  (allA_succ_of_accept 69 70 261 (Polychromatic418967fa.accept_13_4_5_1_1_833 69 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 261 (accept_3_5 68 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 261 (Polychromatic418967fa.accept_12_6_10_9_1_531
  66 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 261 (accept_3_5 65
  70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 261
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 64 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 261 (accept_3_5 62 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 70 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 70 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  60 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 261 (accept_3_5 59
  70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 261
  (Polychromatic418967fa.accept_13_6_5_1_1_834 58 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 70 261 (Polychromatic418967fa.accept_15_12_10_6_1_2134 57 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 261 (accept_3_5 56 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 261 (Polychromatic418967fa.accept_12_6_10_9_1_531
  54 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 261 (accept_3_5 53
  70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 261
  (Polychromatic418967fa.accept_16_4_6_5_1_2245 52 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 70 261 (accept_3_5 50 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 70 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382
  48 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 261 (accept_3_5 47
  70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 261
  (Polychromatic418967fa.accept_15_1_10_6_1_631 46 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 70 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 261 (accept_3_5 44 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 261 (Polychromatic418967fa.accept_12_6_10_9_1_531
  42 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 261 (accept_3_5 41
  70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 261
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 261 (accept_3_5 38 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 70 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 261 (Polychromatic418967fa.accept_16_4_6_5_1_2245
  36 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 261 (accept_3_5 35
  70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 261
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 70 261 (Polychromatic418967fa.accept_15_3_10_6_1_632 33 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 261 (accept_3_5 32 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 261 (Polychromatic418967fa.accept_12_6_10_9_1_531
  30 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 261 (accept_3_5 29
  70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 261
  (Polychromatic418967fa.accept_25_3_20_11_1_15915 28 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 261 (accept_3_5 26 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 70 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 261
  (Polychromatic418967fa.accept_19_5_13_14_1_6366 24 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 261 (accept_3_5 23 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382 22 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 261 (accept_3_5 20 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 261
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 261 (accept_3_5 17 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 261 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 261 (accept_3_5 14 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 70 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 261
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 261 (accept_3_5 11 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 261 (Polychromatic418967fa.accept_21_10_7_9_1_11527 10 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 261 (accept_3_5 8 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 261 (accept_3_5 5 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  261 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 70 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 70 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 261 (accept_3_5 2 70 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 70 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 261 (allA_succ_of_accept 68 69
  261 (Polychromatic418967fa.accept_10_8_9_1_1_189 68 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 69 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 69 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 261 3 22 23 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 261 3 21 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 62
  69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 261
  (Polychromatic418967fa.accept_11_6_3_8_1_843 61 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 261 3 20 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 58 69 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 261 3 19 23 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 261
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 56 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 261 3 18 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 53
  69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 52 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 261 3 17 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 69 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 261 3 16 23 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 261
  (Polychromatic418967fa.accept_18_11_15_9_1_360 47 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 261 3 15 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 261 (Polychromatic418967fa.accept_13_5_4_1_1_364 44
  69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 261 3 14 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 261 (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 261 (Polychromatic418967fa.accept_18_4_15_9_1_6882 40 69
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 261 3 13 23 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 261 (Polychromatic418967fa.accept_17_3_1_6_1_251 37 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 261 3 12 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 35
  69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 261
  (Polychromatic418967fa.accept_15_4_9_6_1_627 34 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 261 3 11 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 69 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 261 3 10 23 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 261 3 9 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 261 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 69 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 261 3 8 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 261 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 69 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 261 3 7 23 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 261
  (Polychromatic418967fa.accept_17_3_1_6_1_251 20 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 261 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 261 3 6 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 69 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 261
  (Polychromatic418967fa.accept_11_5_3_8_1_454 16 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 261 3 5 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 261 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 261 (Polychromatic418967fa.accept_19_13_12_14_1_9217 13 69
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 261 3 4 23 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 261 3 3 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 69 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 261
  (Polychromatic418967fa.accept_19_7_12_14_1_9206 7 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 261 3 2 23 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 69 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 261 3 1 23 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 261
  (Polychromatic418967fa.accept_10_2_9_1_1_185 2 69 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 69 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 261 (allA_succ_of_accept 67 68 261 (accept_3_4 67 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 68 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 68 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 261 (accept_3_4 64 68 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 261 (Polychromatic418967fa.accept_10_3_8_1_1_182
  63 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 261
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 62 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 261 (accept_3_4 61 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 261 (accept_3_4 58 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 68 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 261
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 56 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 261 (accept_3_4 55 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 261 (accept_3_4 52 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 261 (Polychromatic418967fa.accept_20_11_8_1_1_13181 51 68 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 261
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 50 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 261 (accept_3_4 49 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 261 (Polychromatic418967fa.accept_27_21_14_18_1_15914 48 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 261 (accept_3_4 46 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 68 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 261
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 261 (accept_3_4 43 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 261 (accept_3_4 40 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 68 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 261 (accept_3_4 37 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 261 (Polychromatic418967fa.accept_19_17_11_14_1_7858 36 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 261 (accept_3_4 34 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 68 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 261 (accept_3_4 31 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 261 (accept_3_4 28 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 68 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 261
  (Polychromatic418967fa.accept_19_7_11_14_1_11901 26 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 68 261 (accept_3_4 25 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 68 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 68 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 261 (accept_3_4 22 68 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 261 (Polychromatic418967fa.accept_14_7_12_9_1_2926
  21 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 261
  (Polychromatic418967fa.accept_13_7_3_1_1_814 20 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 261 (accept_3_4 19 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 261 (accept_3_4 16 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 261 (Polychromatic418967fa.accept_13_2_3_1_1_3823 15 68 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 261
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 261 (accept_3_4 13 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 261 (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 261 (accept_3_4 10 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 68 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 261
  (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 261 (accept_3_4 7 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  261 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 261 (accept_3_4 4 68 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 261 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2
  68 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 261 (accept_3_4 1 68 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 261 (allA_succ_of_accept 66 67
  261 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 261 (accept_3_5 65 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 261 (accept_3_5 62 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 261
  (Polychromatic418967fa.accept_17_9_16_6_1_4820 60 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 261 (accept_3_5 59 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 261 (Polychromatic418967fa.accept_15_12_7_6_1_4013 57 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 261 (accept_3_5 56 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 67 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 261 (accept_3_5 53 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 261 (accept_3_5 50 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 261 (Polychromatic418967fa.accept_27_22_13_18_1_15913 49 67 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 261 (accept_3_5 47 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 261 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 261 (accept_3_5 44 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 261 (Polychromatic418967fa.accept_15_13_7_6_1_682 43 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 261 (accept_3_5 41 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 261 (accept_3_5 38 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 261
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 261 (accept_3_5 35 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 261 (accept_3_5 32 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 261 (Polychromatic418967fa.accept_15_1_7_6_1_6127 31 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 261 (accept_3_5 29 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 261 (accept_3_5 26 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 261 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 261
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 261 (accept_3_5 23 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 261 (Polychromatic418967fa.accept_18_3_13_9_1_4260 21 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 261 (accept_3_5 20 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 67 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 261 (accept_3_5 17 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 261 (accept_3_5 14 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 261 (accept_3_5 11 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 261 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 261 (accept_3_5 8 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 261 (Polychromatic418967fa.accept_17_7_16_6_1_3705 7 67 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 261 (accept_3_5 5 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 67 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 261 (accept_3_5 2 67 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 261 (Polychromatic418967fa.accept_15_1_7_6_1_6127 1 67 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 261 (allA_succ_of_accept 65 66
  261 (Polychromatic418967fa.accept_10_5_6_1_1_836 65 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 66 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 66 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 261 3 21 22 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 66 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 261 3 20 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 59
  66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 261
  (Polychromatic418967fa.accept_12_10_6_9_1_549 58 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 66 261 3 19 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 66 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 261 3 18 22 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 261
  (Polychromatic418967fa.accept_18_17_12_9_1_3031 53 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 66 261 3 17 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 66 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 50
  66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 261
  (Polychromatic418967fa.accept_19_11_9_14_1_6386 49 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 261 3 16 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 66 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 261 3 15 22 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 66 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 261 3 14 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 41
  66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 66 261 3 13 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 66 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 261 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 261 3 12 22 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 261 3 11 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  32 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 261 3 10 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 261 3 9 22 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 261 3 8 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 22 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 66 261 3 7 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 66 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 261 3 6 22 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 261
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 66 261 3 5 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 66 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 261 3 4 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 261 3 3 22 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 261 3 2 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 66 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 66 261 3 1 22 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 66 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 66 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 66 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 261 (allA_succ_of_accept 64 65 261
  (accept_3_4 64 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 261
  (Polychromatic418967fa.accept_12_3_5_9_1_176 63 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 261 (accept_3_4 61 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  59 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 261 (accept_3_4 58
  65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 261
  (Polychromatic418967fa.accept_15_12_5_6_1_2148 57 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 261 (accept_3_4 55 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 261 (Polychromatic418967fa.accept_11_9_10_8_1_444
  53 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 261 (accept_3_4 52
  65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 261
  (Polychromatic418967fa.accept_12_3_5_9_1_176 51 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 261 (accept_3_4 49 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 65 261 (Polychromatic418967fa.accept_15_3_5_6_1_4005 48 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 261 (Polychromatic418967fa.accept_16_15_1_5_1_2265
  47 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 261 (accept_3_4 46
  65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 261
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 261 (accept_3_4 43 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 65 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 261 (Polychromatic418967fa.accept_15_11_5_6_1_669
  41 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 261 (accept_3_4 40
  65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 261 (accept_3_4 37 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 65 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 261 (Polychromatic418967fa.accept_20_15_5_1_1_5899
  35 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 261 (accept_3_4 34
  65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 261
  (Polychromatic418967fa.accept_15_3_5_6_1_4005 33 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 261 (accept_3_4 31 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 65 261 (Polychromatic418967fa.accept_18_12_11_9_1_4257 30 65 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 261 (accept_3_4 28 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 261 (accept_3_4 25 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 65 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 261
  (Polychromatic418967fa.accept_19_4_8_14_1_3538 23 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 261 (accept_3_4 22 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 261 (Polychromatic418967fa.accept_19_2_8_14_1_3648 21 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 261 (accept_3_4 19 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 261 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 65 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 261
  (Polychromatic418967fa.accept_21_17_2_9_1_6867 17 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 261 (accept_3_4 16 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 261 (accept_3_4 13 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 65 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 261
  (Polychromatic418967fa.accept_15_11_5_6_1_669 11 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 261 (accept_3_4 10 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 261 (accept_3_4 7 65 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 65 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 261
  (Polychromatic418967fa.accept_19_5_8_14_1_6384 5 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 261 (accept_3_4 4 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  261 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 65 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 261 (accept_3_4 1 65 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 261
  (allA_succ_of_accept 63 64 261 (Polychromatic418967fa.accept_13_11_12_1_1_2154 63 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 261 (accept_3_5 62 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662
  60 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 261 (accept_3_5 59
  64 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 261
  (Polychromatic418967fa.accept_15_13_4_6_1_3046 58 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 64 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 261 (accept_3_5 56 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974
  54 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 261 (accept_3_5 53
  64 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 64 261 (Polychromatic418967fa.accept_18_15_10_9_1_2009 51 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 261 (accept_3_5 50 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 48
  64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 261 (accept_3_5 47 64
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 261
  (Polychromatic418967fa.accept_19_8_7_14_1_13279 46 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 64 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 261 (accept_3_5 44 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 261 (Polychromatic418967fa.accept_12_6_4_9_1_544
  42 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 261 (accept_3_5 41
  64 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 261
  (Polychromatic418967fa.accept_15_10_4_6_1_2129 40 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 64 261 (Polychromatic418967fa.accept_15_9_4_6_1_3075 39 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 261 (accept_3_5 38 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 261 (Polychromatic418967fa.accept_17_2_13_6_1_3772
  36 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 261 (accept_3_5 35
  64 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 64 261 (Polychromatic418967fa.accept_18_15_10_9_1_2009 33 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 261 (accept_3_5 32 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 261 (Polychromatic418967fa.accept_12_6_4_9_1_544
  30 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 261 (accept_3_5 29
  64 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 261
  (Polychromatic418967fa.accept_13_2_12_1_1_343 28 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 64 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 261 (accept_3_5 26 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 24
  64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 261 (accept_3_5 23 64
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 261
  (Polychromatic418967fa.accept_19_3_7_14_1_3669 22 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 64 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 261 (accept_3_5 20 64 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 261 (Polychromatic418967fa.accept_12_6_4_9_1_544
  18 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 261 (accept_3_5 17
  64 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 261
  (Polychromatic418967fa.accept_23_16_18_8_1_15912 16 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 261 (accept_3_5 14 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 261
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 261 (accept_3_5 11 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 261 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 261 (accept_3_5 8 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 261 (accept_3_5 5 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  261 (Polychromatic418967fa.accept_19_4_7_14_1_3537 4 64 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 64 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 261 (accept_3_5 2 64 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 261 (allA_succ_of_accept 62 63 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 261 3 20 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  59 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 261 3 19 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 261 (Polychromatic418967fa.accept_15_11_3_6_1_1306 56 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 261 9 6 7 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 53 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 52 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 261 3 17 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 261 3 16 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 261 9 5 7 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 261
  (Polychromatic418967fa.accept_14_2_7_9_1_2937 44 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 261 3 14 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 261
  (Polychromatic418967fa.accept_14_12_7_9_1_726 40 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 261 3 13 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 261 9 4 7 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 261 3 11 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 32
  63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 261 3 10 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 261 9 3 7 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 261 3 8 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 261 3 7 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 261 (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 261 9 2 7 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 261 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 261 3 5 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 261 3 4 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 261 9 1 7 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 261
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 261 3 2 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 261
  (Polychromatic418967fa.accept_16_4_15_5_1_5537 4 63 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 261 3 1 21 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 261 (allA_succ_of_accept 61 62 261
  (accept_3_4 61 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 261 (accept_3_4 58 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 261 (Polychromatic418967fa.accept_10_6_2_1_1_494
  56 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 261 (accept_3_4 55
  62 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 261
  (Polychromatic418967fa.accept_12_6_2_9_1_537 54 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 261 (accept_3_4 52 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 50
  62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 261 (accept_3_4 49 62
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 261
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 261 (accept_3_4 46 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 261 (Polychromatic418967fa.accept_19_6_5_14_1_3582
  44 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 261 (accept_3_4 43
  62 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 261
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 261 (accept_3_4 40 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 261 (accept_3_4 37 62
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 261 (Polychromatic418967fa.accept_7_1_6_2_1_18
  36 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 261 (accept_3_4 34 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 261 (accept_3_4 31 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 62 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 261 (accept_3_4 28 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 261 (accept_3_4 25 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 62 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 261 (accept_3_4 22 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 261 (Polychromatic418967fa.accept_17_4_11_6_1_3730 21 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 261 (Polychromatic418967fa.accept_25_20_12_11_1_15911 20 62 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 261 (accept_3_4 19 62 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 62 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 261 (accept_3_4 16 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 261 (Polychromatic418967fa.accept_21_14_20_9_1_5306 14 62 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 261 (accept_3_4 13 62 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 261 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 62
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 261 (accept_3_4 10 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 261 (accept_3_4 7 62 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 62 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 261 (accept_3_4 4 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 261 (Polychromatic418967fa.accept_19_2_5_14_1_10644 2 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 261 (accept_3_4 1 62 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 261
  (allA_succ_of_accept 60 61 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 61 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 61 261 (accept_3_5 59 61 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 61 261 (Polychromatic418967fa.accept_13_5_9_1_1_1405
  57 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 261 (accept_3_5 56
  61 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 261
  (Polychromatic418967fa.accept_15_10_1_6_1_3033 55 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 61 261 (Polychromatic418967fa.accept_13_2_9_1_1_67 54 61 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 61 261 (accept_3_5 53 61 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 61 261 (Polychromatic418967fa.accept_12_3_1_9_1_202
  51 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 261 (accept_3_5 50
  61 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 261
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 49 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 61 261 (Polychromatic418967fa.accept_15_3_1_6_1_206 48 61 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 61 261 (accept_3_5 47 61 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 61 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 45
  61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 261 (accept_3_5 44 61
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 261
  (Polychromatic418967fa.accept_22_21_17_19_1_15910 43 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 61 261 (Polychromatic418967fa.accept_16_10_13_5_1_3292 42 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 61 261 (accept_3_5 41 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 61 261 (accept_3_5 38 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  61 261 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 61 261 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 61 261 (accept_3_5 35 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 61 261
  (Polychromatic418967fa.accept_15_3_1_6_1_206 33 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 61 261 (accept_3_5 32 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  61 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 61 261 (Polychromatic418967fa.accept_22_8_17_19_1_15909 30 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 61 261 (accept_3_5 29 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 61 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 61 261 (accept_3_5 26 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  61 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 61 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 61 261 (accept_3_5 23 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 261
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 61 261 (accept_3_5 20 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  61 261 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 61 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 61 261 (accept_3_5 17 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 61 261 (accept_3_5 14 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  61 261 (Polychromatic418967fa.accept_19_13_4_14_1_11912 13 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 61 261 (Polychromatic418967fa.accept_17_12_10_6_1_3691 12 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 61 261 (accept_3_5 11 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 261
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 61 261 (accept_3_5 8 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61
  261 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 61 261 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 61 261 (accept_3_5 5 61 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 61 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 61 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 61 261 (accept_3_5 2 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 61
  261 (Polychromatic418967fa.accept_16_1_13_5_1_2280 1 61 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 61 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 261
  (allA_succ_of_accept 59 60 261 (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 58 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 60 261 3 19 20 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 60 261
  (Polychromatic418967fa.accept_16_8_12_5_1_200 56 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 60 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 261 3 18 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 261 (Polychromatic418967fa.accept_21_11_18_9_1_465
  53 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 261
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 52 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 60 261 3 17 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 60 261 (Polychromatic418967fa.accept_13_11_8_1_1_3815 50 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 261 3 16 20 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 261 3 15 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 261 (Polychromatic418967fa.accept_13_5_8_1_1_2161
  44 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 261
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 43 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 261 3 14 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 60 261 3 13 20 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 60 261
  (Polychromatic418967fa.accept_13_12_8_1_1_825 38 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 261 (Polychromatic418967fa.accept_13_11_8_1_1_3815 37 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 261 3 12 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 35
  60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 34 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 60 261 3 11 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 60 261 (Polychromatic418967fa.accept_13_6_8_1_1_2913 32 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 261 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 261 3 10 20 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 261
  (Polychromatic418967fa.accept_21_8_18_9_1_5329 29 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 261 (Polychromatic418967fa.accept_19_9_3_14_1_2400 28 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 261 3 9 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 261
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 261 3 8 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 261 (Polychromatic418967fa.accept_16_7_12_5_1_734 23 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 261 (Polychromatic418967fa.accept_13_9_8_1_1_824 22 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 261 3 7 20 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 60 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 261 3 6 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 261
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 60 261 3 5 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 60 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 261 3 4 20 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 261
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 261 (Polychromatic418967fa.accept_16_10_12_5_1_2254 10 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 261 3 3 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 261 (Polychromatic418967fa.accept_16_8_12_5_1_200 8 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 261
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 261 3 2 20 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 261 (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 60 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 261 3 1 20 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 261
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 60 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 60 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 261 (allA_succ_of_accept 58 59 261 (accept_3_4 58 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 59 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 59 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 59 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 261 (accept_3_4 55 59 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 261
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 53 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 261 (accept_3_4 52 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 261 (accept_3_4 49 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 261 (accept_3_4 46 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 261 (accept_3_4 43 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 261 (accept_3_4 40 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 261 (accept_3_4 37 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 261 (accept_3_4 34 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 261 (accept_3_4 31 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 261 (accept_3_4 28 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 261 (accept_3_4 25 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 261 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 59 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 261
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 261 (accept_3_4 22 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 261 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 261 (accept_3_4 19 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 261
  (Polychromatic418967fa.accept_19_17_2_14_1_11897 17 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 59 261 (accept_3_4 16 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 59 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 59 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 261 (accept_3_4 13 59 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12
  59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 261
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 261 (accept_3_4 10 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 261 (accept_3_4 7 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 261 (accept_3_4 4 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  261 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 59 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 261 (accept_3_4 1 59 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 261
  (allA_succ_of_accept 57 58 261 (Polychromatic418967fa.accept_13_5_6_1_1_822 57 58 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 261 (accept_3_5 56 58 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 261 (Polychromatic418967fa.accept_12_6_10_9_1_531
  54 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 261 (accept_3_5 53
  58 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 261
  (Polychromatic418967fa.accept_15_7_13_6_1_696 52 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 261 (accept_3_5 50 58 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902
  48 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 261 (accept_3_5 47
  58 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 261
  (Polychromatic418967fa.accept_13_7_6_1_1_368 46 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 261 (Polychromatic418967fa.accept_16_13_10_5_1_2278 45 58 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 261 (accept_3_5 44 58 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 261 (Polychromatic418967fa.accept_12_6_10_9_1_531
  42 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 261 (accept_3_5 41
  58 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 261
  (Polychromatic418967fa.accept_19_2_1_14_1_3663 40 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 261 (accept_3_5 38 58 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 58 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 261
  (Polychromatic418967fa.accept_19_17_1_14_1_6360 36 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 261 (accept_3_5 35 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 34 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 261 (accept_3_5 32 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 29 58 261 29 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 28 58 261 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 58 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 261 (accept_3_5 26 58 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25
  58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 261
  (Polychromatic418967fa.accept_21_3_16_9_1_8528 24 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 261 (accept_3_5 23 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 22 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 261 (accept_3_5 20 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 261 (accept_3_5 17 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 261 (accept_3_5 14 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 261
  (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 261 (accept_3_5 11 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 261 (Polychromatic418967fa.accept_19_10_1_14_1_9224 10 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 261 (accept_3_5 8 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 261
  (Polychromatic418967fa.accept_11_6_3_8_1_843 6 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 261 (accept_3_5 5 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  261 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 58 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 261 (accept_3_5 2 58 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 261 (allA_succ_of_accept 56 57 261
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 261 3 18 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 261 (Polychromatic418967fa.accept_21_11_15_9_1_3868
  53 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 261 3 17 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 261 (Polychromatic418967fa.accept_14_8_1_9_1_2085 50 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 57 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 261 3 16 19 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 261
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 47 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 46 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 261 3 15 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 44
  57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 261
  (Polychromatic418967fa.accept_13_4_5_1_1_833 43 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 261 3 14 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 261 (Polychromatic418967fa.accept_15_10_12_6_1_3000 40 57
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 261 3 13 19 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 261 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 261 3 12 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382
  35 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 261 3 11 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 261 (Polychromatic418967fa.accept_13_6_5_1_1_834 32 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 57 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 261 3 10 19 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 261
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 261 3 9 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 57 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 261
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 261 3 8 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 261 (Polychromatic418967fa.accept_21_2_15_9_1_3838 23 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382 22 57 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 261 3 7 19 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 261 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 261 3 6 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 57 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 261
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 261 3 5 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 261 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 57 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 261 3 4 19 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 261
  (Polychromatic418967fa.accept_16_11_9_5_1_4412 11 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 261 3 3 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 57 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 261
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 261 3 2 19 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 57 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 261 3 1 19 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 261
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 57 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 261 (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 57 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 261 (allA_succ_of_accept 55 56 261 (accept_3_4 55 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 56 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 261 (accept_3_4 52 56 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 261 (Polychromatic418967fa.accept_16_3_8_5_1_6790
  51 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 261
  (Polychromatic418967fa.accept_15_5_11_6_1_692 50 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 261 (accept_3_4 49 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 48 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 261 (accept_3_4 46 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 56 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 261
  (Polychromatic418967fa.accept_13_5_4_1_1_364 44 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 261 (accept_3_4 43 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 261 (accept_3_4 40 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 56 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 261
  (Polychromatic418967fa.accept_17_4_5_6_1_8717 38 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 261 (accept_3_4 37 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 261 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 261 (accept_3_4 34 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 261 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 56 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 261 (accept_3_4 31 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 261 (accept_3_4 28 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 261 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 56 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 261
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 261 (accept_3_4 25 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 261 (accept_3_4 22 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 261 (Polychromatic418967fa.accept_17_4_5_6_1_8717 21 56 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 261
  (Polychromatic418967fa.accept_15_5_11_6_1_692 20 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 261 (accept_3_4 19 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 261 (accept_3_4 16 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 56 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 261
  (Polychromatic418967fa.accept_24_14_8_21_1_15908 14 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 56 261 (accept_3_4 13 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 56 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 56 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 261 (accept_3_4 10 56 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 9
  56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 261
  (Polychromatic418967fa.accept_31_8_25_13_1_15907 8 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 261 (accept_3_4 7 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  261 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 261 (accept_3_4 4 56 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 261 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 56 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  56 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 261 (accept_3_4 1 56 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 261 (allA_succ_of_accept 54 55 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 261 (accept_3_5 53 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 261
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 261 (accept_3_5 50 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 261 (Polychromatic418967fa.accept_15_3_10_6_1_632 48 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 261 (accept_3_5 47 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 261 (accept_3_5 44 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 261 (accept_3_5 41 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 261 (accept_3_5 38 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 261 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 261 (accept_3_5 35 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 261
  (Polychromatic418967fa.accept_13_7_3_1_1_814 33 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 261 (accept_3_5 32 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 261 (accept_3_5 29 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 261
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 261 (accept_3_5 26 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 261 (accept_3_5 23 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 261
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 21 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 261 (accept_3_5 20 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 261 (accept_3_5 17 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 261 (accept_3_5 14 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 261 (Polychromatic418967fa.accept_22_13_11_19_1_8148 13 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 261 (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 261 (accept_3_5 11 55 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 261 (accept_3_5 8 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  261 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 55 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 261 (accept_3_5 5 55 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 55
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 261 (accept_3_5 2 55 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 55
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 261 (allA_succ_of_accept 53 54 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 261 3 17 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 50
  54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 261
  (Polychromatic418967fa.accept_14_7_12_9_1_2926 49 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 261 3 16 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 54 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 261 9 5 6 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 261 3 14 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 261 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  41 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 54 261 3 13 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 54 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 54 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 261 9 4 6 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 261 3 11 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 261 3 10 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 261 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 54 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 261 9 3 6 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 261 3 8 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 261
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 261 3 7 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 261 9 2 6 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 261 3 5 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 54 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 261
  (Polychromatic418967fa.accept_19_13_16_14_1_3517 13 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 54 261 3 4 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 54 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 10
  54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 261 9 1 6 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 261 3 2 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 54 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 54 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 261 3 1 18 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 54 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 261 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 54 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 261 (allA_succ_of_accept 52 53 261 (accept_3_4
  52 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 261
  (Polychromatic418967fa.accept_12_3_5_9_1_176 51 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 261 (accept_3_4 49 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 261 (accept_3_4 46 53
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 261
  (Polychromatic418967fa.accept_19_7_15_14_1_3659 45 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 261 (accept_3_4 43 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 53 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 41
  53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 261 (accept_3_4 40 53
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 261
  (Polychromatic418967fa.accept_12_3_5_9_1_176 39 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 261 (accept_3_4 37 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 261 (Polychromatic418967fa.accept_19_17_15_14_1_3623 36 53 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 261
  (Polychromatic418967fa.accept_17_1_2_6_1_818 35 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 261 (accept_3_4 34 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 261 (accept_3_4 31 53 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 261 (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 53 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 261
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 29 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 261 (accept_3_4 28 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 261 (accept_3_4 25 53 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 261 (Polychromatic418967fa.accept_23_1_7_8_1_9423 24 53 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 261
  (Polychromatic418967fa.accept_19_4_15_14_1_10614 23 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 53 261 (accept_3_4 22 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 53 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 261 (accept_3_4 19 53 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  18 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 261
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 261 (accept_3_4 16 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 261 (accept_3_4 13 53 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 261
  (Polychromatic418967fa.accept_19_11_15_14_1_5018 11 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 53 261 (accept_3_4 10 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 53 261 (Polychromatic418967fa.accept_23_9_7_8_1_15906 9 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 261 (accept_3_4 7 53 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 261 (accept_3_4 4 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  261 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 53 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 261 (accept_3_4 1 53 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 261))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 261
  (allA_succ_of_accept 51 52 261 (Polychromatic418967fa.accept_18_15_16_9_1_4299 51 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 261 (accept_3_5 50 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 48
  52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 261 (accept_3_5 47 52
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 261 (Polychromatic418967fa.accept_21_3_10_9_1_14437 45 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 261 (accept_3_5 44 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 261 (Polychromatic418967fa.accept_12_6_4_9_1_544
  42 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 261 (accept_3_5 41
  52 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 52 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 261 (accept_3_5 38 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 52 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 36
  52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 261 (accept_3_5 35 52
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 52 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 261 (accept_3_5 32 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 52 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 261 (Polychromatic418967fa.accept_12_6_4_9_1_544
  30 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 261 (accept_3_5 29
  52 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 261
  (Polychromatic418967fa.accept_15_13_7_6_1_682 28 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 52 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 261 (accept_3_5 26 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 52 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 261 (Polychromatic418967fa.accept_16_8_4_5_1_4379
  24 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 261 (accept_3_5 23
  52 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 22 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 52 261 (Polychromatic418967fa.accept_22_21_8_19_1_15905 21 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 261 (accept_3_5 20 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 52 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 261 (Polychromatic418967fa.accept_12_6_4_9_1_544
  18 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 261 (accept_3_5 17
  52 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 16 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 52 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 261 (accept_3_5 14 52 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 52 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12
  52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 261 (accept_3_5 11 52
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 261
  (Polychromatic418967fa.accept_22_10_8_19_1_12892 10 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 261 (accept_3_5 8 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 261 (accept_3_5 5 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  261 (Polychromatic418967fa.accept_25_4_2_11_1_15904 4 52 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 261 (accept_3_5 2 52 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  261)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 261 (allA_succ_of_accept 50 51 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 261 3 16 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  47 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 261 3 15 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 261 (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 51 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 261 3 14 17 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 261 (Polychromatic418967fa.accept_16_8_3_5_1_5512 40 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 261 3 13 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 261
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 261 3 12 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 261 3 11 17 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 261
  (Polychromatic418967fa.accept_20_12_11_1_1_3032 32 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 261 3 10 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 29
  51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 261
  (Polychromatic418967fa.accept_13_2_12_1_1_343 28 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 261 3 9 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 51 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 261 3 8 17 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 261 3 7 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 261 (Polychromatic418967fa.accept_19_1_13_14_1_3509 20 51
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 261 3 6 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 261 (Polychromatic418967fa.accept_18_16_15_9_1_6852 16 51
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 261 3 5 17 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 261 3 4 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 51 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 261 3 3 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 261 3 2 17 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 51 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 261 3 1 17 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 51 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 261))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 261 (allA_succ_of_accept 49 50 261
  (accept_3_4 49 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 261 (accept_3_4 46 50 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 50 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 261 (Polychromatic418967fa.accept_15_14_5_6_1_6168
  44 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 261 (accept_3_4 43
  50 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 261
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 261 (accept_3_4 40 50 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 38
  50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 261 (accept_3_4 37 50
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 261
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 261 (accept_3_4 34 50 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 261 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 50 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 261
  (Polychromatic418967fa.accept_19_13_12_14_1_9217 32 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 50 261 (accept_3_4 31 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 50 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 50 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 50 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 261 (accept_3_4 28 50 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 261
  (Polychromatic418967fa.accept_15_11_5_6_1_669 26 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 261 (accept_3_4 25 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 261 (accept_3_4 22 50 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 261 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 50 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 261 (accept_3_4 19 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 261 (accept_3_4 16 50 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 261
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 261 (accept_3_4 13 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 261 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 261 (accept_3_4 10 50 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 261 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 50 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 261
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 261 (accept_3_4 7 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  261 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 50 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 261 (accept_3_4 4 50 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 261
  (Polychromatic418967fa.accept_19_2_12_14_1_11919 2 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 261 (accept_3_4 1 50 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  261)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 261 (allA_succ_of_accept 48 49 261
  (Polychromatic418967fa.accept_10_8_9_1_1_189 48 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 261 (accept_3_5 47 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 261 (accept_3_5 44 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 261 (Polychromatic418967fa.accept_13_4_10_1_1_1390 43 49 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 261
  (Polychromatic418967fa.accept_10_2_9_1_1_185 42 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 261 (accept_3_5 41 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 261 (accept_3_5 38 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 261 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 49 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 261 (accept_3_5 35 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 261 (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 261 (accept_3_5 32 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 261 (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 49 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 261
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 261 (accept_3_5 29 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 261 (accept_3_5 26 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 49 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 261
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 261 (accept_3_5 23 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 261 (Polychromatic418967fa.accept_18_3_13_9_1_4260 21 49 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 261 (accept_3_5 20 49 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 261 (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 49 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 261
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 261 (accept_3_5 17 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 261 (accept_3_5 14 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 49 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 261 (accept_3_5 11 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 261 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 261 (accept_3_5 8 49 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 261 (Polychromatic418967fa.accept_19_7_11_14_1_11901 7 49 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 261
  (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 261 (accept_3_5 5 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 49 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 261 (accept_3_5 2 49 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 261 (Polychromatic418967fa.accept_25_1_24_11_1_15903 1 49 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 261)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 261 (allA_succ_of_accept 47 48 261 (Polychromatic418967fa.accept_13_8_9_1_1_2147 47 48 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 46 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 48 261 3 15 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 48 261 (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 48 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 261 3 14 16 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 261
  (Polychromatic418967fa.accept_13_2_9_1_1_67 41 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 261 3 13 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 261
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 261 3 12 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 261 (Polychromatic418967fa.accept_15_5_3_6_1_2128 35 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 48 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 261 3 11 16 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 261 3 10 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 261
  (Polychromatic418967fa.accept_13_2_9_1_1_67 28 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 48 261 3 9 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 48 261 (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 48 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 261 3 8 16 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 261
  (Polychromatic418967fa.accept_10_3_8_1_1_182 23 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 261 3 7 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 261 (Polychromatic418967fa.accept_15_5_3_6_1_2128 20 48 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 261
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 261 3 6 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 261 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 48 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 261 3 5 16 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 261
  (Polychromatic418967fa.accept_21_14_6_9_1_14343 14 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 261 3 4 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 10 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 48 261 3 3 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 48 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 48 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 261 3 2 16 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 261
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 48 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 261 3 1 16 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 261 (Polychromatic418967fa.accept_13_2_9_1_1_67 2 48 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 261)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 261 (allA_succ_of_accept 46 47 261
  (accept_3_4 46 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 261 (accept_3_4 43 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 261 (Polychromatic418967fa.accept_15_11_2_6_1_3010
  41 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 261 (accept_3_4 40
  47 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 261 (accept_3_4 37 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 47 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 261 (Polychromatic418967fa.accept_13_9_8_1_1_824
  35 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 261 (accept_3_4 34
  47 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 261
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 261 (accept_3_4 31 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 261 (Polychromatic418967fa.accept_22_7_3_19_1_8158
  29 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 261 (accept_3_4 28
  47 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 261
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 261 (accept_3_4 25 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 261 (Polychromatic418967fa.accept_15_8_2_6_1_2125
  23 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 261 (accept_3_4 22
  47 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 261
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 21 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 261 (accept_3_4 19 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 261 (accept_3_4 16 47
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 261
  (Polychromatic418967fa.accept_12_3_11_9_1_193 15 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 261 (accept_3_4 13 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 261 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 47 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 11
  47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 261 (accept_3_4 10 47
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 261
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 261 (accept_3_4 7 47 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 5
  47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 261 (accept_3_4 4 47 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 261 (accept_3_4 1 47 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  261))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 261 (allA_succ_of_accept 45 46 261
  (Polychromatic418967fa.accept_10_5_6_1_1_836 45 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 261 (accept_3_5 44 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 46 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 261 (accept_3_5 41 46 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 46 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 261 (accept_3_5 38 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 261 (Polychromatic418967fa.accept_17_2_12_6_1_3737 36 46 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 261 (accept_3_5 35 46 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 46 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 261 (accept_3_5 32 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 261 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 46 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 261 (accept_3_5 29 46 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 261 (Polychromatic418967fa.accept_17_11_12_6_1_6070 28 46 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 261 (accept_3_5 26 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 261 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 46 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 261 (accept_3_5 23 46 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 46 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 261
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 261 (accept_3_5 20 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 261 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 46 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 261 (accept_3_5 17 46 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 46 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 261 (accept_3_5 14 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 46 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 261 (accept_3_5 11 46 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 261 (Polychromatic418967fa.accept_15_10_1_6_1_3033 10 46 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 261
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 261 (accept_3_5 8 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 46 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 261 (accept_3_5 5 46 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 261 (Polychromatic418967fa.accept_19_4_8_14_1_3538 4 46 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 261 (accept_3_5 2 46 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  261)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 261 (allA_succ_of_accept 44 45 261
  (Polychromatic418967fa.accept_10_4_5_1_1_497 44 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 261 3 14 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 41
  45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 261 3 13 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 261 (Polychromatic418967fa.accept_17_4_11_6_1_3730 38 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 45 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 261 9 4 5 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 261
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 261 3 11 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 261
  (Polychromatic418967fa.accept_22_10_1_19_1_15902 32 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 45 261 (Polychromatic418967fa.accept_13_5_6_1_1_822 31 45 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 261 3 10 15 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 261 (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 261 9 3 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 45 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 261
  (Polychromatic418967fa.accept_16_9_13_5_1_2238 25 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 45 261 3 8 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 45 261 (Polychromatic418967fa.accept_19_4_7_14_1_3537 23 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 45 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 261 3 7 15 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 261 9 2 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 261 (Polychromatic418967fa.accept_16_1_13_5_1_2280 17 45 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 261
  (Polychromatic418967fa.accept_10_6_5_1_1_482 16 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 261 3 5 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 45 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 261 3 4 15 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 261
  (Polychromatic418967fa.accept_19_11_7_14_1_6394 11 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 261 (Polychromatic418967fa.accept_16_10_13_5_1_3292 10 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 261 9 1 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 261
  (Polychromatic418967fa.accept_13_7_6_1_1_368 7 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 45 261 3 2 15 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 45 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 45 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 261 3 1 15 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 261
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 45 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 45 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 45 261))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 261
  (allA_succ_of_accept 43 44 261 (accept_3_4 43 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  44 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 261 (accept_3_4 40 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 261 (Polychromatic418967fa.accept_14_11_2_9_1_5873 39 44 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 261
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 38 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 261 (accept_3_4 37 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 261 (Polychromatic418967fa.accept_16_4_12_5_1_2287 36 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 261 (accept_3_4 34 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 44 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 261
  (Polychromatic418967fa.accept_13_6_5_1_1_834 32 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 261 (accept_3_4 31 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 261 (accept_3_4 28 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 44 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 261
  (Polychromatic418967fa.accept_16_10_12_5_1_2254 26 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 261 (accept_3_4 25 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 261 (accept_3_4 22 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 44 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 261
  (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 261 (accept_3_4 19 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 261 (accept_3_4 16 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 44 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 261
  (Polychromatic418967fa.accept_21_14_2_9_1_6864 14 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 261 (accept_3_4 13 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 261 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 261 (accept_3_4 10 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 44 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 261
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 261 (accept_3_4 7 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  261 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 261 (accept_3_4 4 44 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 261 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 44 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 261 (Polychromatic418967fa.accept_26_2_18_1_1_15901
  2 44 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 261 (accept_3_4 1 44
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 261)))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  43 261 (allA_succ_of_accept 42 43 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 261 (accept_3_5 41 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  39 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 261 (accept_3_5 38
  43 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 261
  (Polychromatic418967fa.accept_15_7_13_6_1_696 37 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 43 261 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 261 (accept_3_5 35 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 43 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 261 (Polychromatic418967fa.accept_17_16_9_6_1_3723
  33 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 261 (accept_3_5 32
  43 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 43 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 261 (accept_3_5 29 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 43 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 27
  43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 261 (accept_3_5 26 43
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 261
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 25 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 43 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 261 (accept_3_5 23 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 43 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 261 (Polychromatic418967fa.accept_18_3_7_9_1_5486
  21 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 261 (accept_3_5 20
  43 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 261
  (Polychromatic418967fa.accept_15_4_13_6_1_642 19 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 43 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 261 (accept_3_5 17 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 43 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  15 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 261 (accept_3_5 14
  43 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 43 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 261 (accept_3_5 11 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 43 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 9
  43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 261 (accept_3_5 8 43 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 261 (Polychromatic418967fa.accept_15_7_13_6_1_696 7
  43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 261 (accept_3_5 5 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 261 (accept_3_5 2 43 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 261 (Polychromatic418967fa.accept_25_1_18_11_1_15900 1 43 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 261)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 261 (allA_succ_of_accept 41 42 261 (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 42 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 42 261 3 13 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 42 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 42 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 261 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 42
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 261 3 12 14 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 42 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 261 3 11 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974
  32 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 261 3 10 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 42 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 42 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 261 3 9 14 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 261 (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 42 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 261 3 8 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 261
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 42 261 3 7 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 42 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 261 3 6 14 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 261
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 42 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 261 3 5 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 42 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 261
  (Polychromatic418967fa.accept_10_3_2_1_1_839 13 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 261 3 4 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 42
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 261 3 3 14 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 42 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 261 3 2 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 261 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 42 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 42 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 42 261 3 1 14 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 42 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 42 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 261 (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 42 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  261)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 261 (allA_succ_of_accept 40 41 261 (accept_3_4 40 41 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 39
  41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 261 (accept_3_4 37 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 261 (Polychromatic418967fa.accept_13_9_2_1_1_813 35 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 261 (accept_3_4 34 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 261 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 41 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 261 (accept_3_4 31 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 261 (Polychromatic418967fa.accept_16_14_9_5_1_4388 30 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 261 (accept_3_4 28 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 261 (accept_3_4 25 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 261 (Polychromatic418967fa.accept_21_2_20_9_1_2507 23 41 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 261 (accept_3_4 22 41 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 261 (Polychromatic418967fa.accept_26_21_15_1_1_15899 21 41
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 261 (accept_3_4 19 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 261 (accept_3_4 16 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 41 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 261 (accept_3_4 13 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 261 (accept_3_4 10 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 261 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 41 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 261 (accept_3_4 7 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  261 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 41 261 (Polychromatic418967fa.accept_15_5_11_6_1_692 5 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 261 (accept_3_4 4 41 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 41 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 41 261 (accept_3_4 1 41 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41
  261))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 261 (allA_succ_of_accept 39 40 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 261 (accept_3_5 38 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 261 (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 40 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 261 (accept_3_5 35 40 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 261 (Polychromatic418967fa.accept_15_4_10_6_1_2997 34 40 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 261
  (Polychromatic418967fa.accept_15_3_10_6_1_632 33 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 261 (accept_3_5 32 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 261 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 40 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 261 (accept_3_5 29 40 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 261 (Polychromatic418967fa.accept_16_12_8_5_1_3316 28 40 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 261
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 261 (accept_3_5 26 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 40 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 261 (accept_3_5 23 40 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 261 (Polychromatic418967fa.accept_23_22_17_8_1_15898 22 40 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 261
  (Polychromatic418967fa.accept_14_7_12_9_1_2926 21 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 261 (accept_3_5 20 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 40 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 261 (accept_3_5 17 40 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 261 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 40 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 261
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 261 (accept_3_5 14 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 261 (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 40 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 261 (accept_3_5 11 40 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 40 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 261
  (Polychromatic418967fa.accept_22_9_18_19_1_15897 9 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 261 (accept_3_5 8 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 261 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 40 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 261 (accept_3_5 5 40 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 40 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 40
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 261 (accept_3_5 2 40 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  261)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 261 (allA_succ_of_accept 38 39 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 39 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 261 3 12 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 35
  39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 261 3 11 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 39 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 39 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 261 3 10 13 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 39 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 261 3 9 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 261 3 8 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 39 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 261 3 7 13 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 39 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 261 3 6 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 39 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 261
  (Polychromatic418967fa.accept_14_2_11_9_1_2925 16 39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 261 3 5 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 39 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 261 3 4 13 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 261 3 3 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 39 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 261 3 2 13 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 39 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 261 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 39 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 261 3 1 13 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 39 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 261))))))))))))))))))))))))))))))))))))))) (allB_succ 38 261
  (allA_succ_of_accept 37 38 261 (accept_3_4 37 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 261 (accept_3_4 34 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 38 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 261
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 32 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 261 (accept_3_4 31 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 261 (accept_3_4 28 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 261 (accept_3_4 25 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 261 (accept_3_4 22 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 38 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 261 (accept_3_4 19 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 261 (accept_3_4 16 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 261
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 261 (accept_3_4 13 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 261 (accept_3_4 10 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 38 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 261 (accept_3_4 7 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  261 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 261 (accept_3_4 4 38 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 2
  38 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 261 (accept_3_4 1 38 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 261)))))))))))))))))))))))))))))))))))))) (allB_succ 37 261
  (allA_succ_of_accept 36 37 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 37 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 261 (accept_3_5 35 37 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 261 (Polychromatic418967fa.accept_13_7_11_1_1_2903
  33 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 261 (accept_3_5 32
  37 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 261
  (Polychromatic418967fa.accept_15_1_7_6_1_6127 31 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 261 (Polychromatic418967fa.accept_20_10_17_1_1_8852 30 37 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 261 (accept_3_5 29 37 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 261 (Polychromatic418967fa.accept_12_3_1_9_1_202
  27 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 261 (accept_3_5 26
  37 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 261
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 261 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 37 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 261 (accept_3_5 23 37 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 261 (Polychromatic418967fa.accept_13_8_11_1_1_3789
  21 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 261 (accept_3_5 20
  37 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 261
  (Polychromatic418967fa.accept_27_19_10_18_1_15896 19 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 37 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 261 (accept_3_5 17 37 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 261 (accept_3_5 14 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 261 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 37 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 261 (accept_3_5 11 37 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 261
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 261 (accept_3_5 8 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 37 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 261 (accept_3_5 5 37 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 261 (accept_3_5 2 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 37 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 37 261))))))))))))))))))))))))))))))))))))) (allB_succ 36 261 (allA_succ_of_accept 35 36 261
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 36 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 261 3 11 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  32 36 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 36 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 261 3 10 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 261 (Polychromatic418967fa.accept_14_1_8_9_1_1312 29 36 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 261 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 36 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 261 9 3 4 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 261
  (Polychromatic418967fa.accept_20_6_16_1_1_7262 26 36 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 36 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 261 3 8 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 261 (Polychromatic418967fa.accept_21_2_15_9_1_3838 23 36 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 36 261 3 7 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 36 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 36 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 261 (Polychromatic418967fa.accept_21_19_15_9_1_11533 19 36
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 261 9 2 4 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 36 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 261 3 5 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 261 (Polychromatic418967fa.accept_21_14_15_9_1_1339 14 36
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 36 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 261 3 4 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 261 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 36 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 36 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 261 9 1 4 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 261
  (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 36 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 261 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 261 3 2 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 36 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 261
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 36 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 36 261 3 1 12 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 36 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 36 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 261))))))))))))))))))))))))))))))))))))
  (allB_succ 35 261 (allA_succ_of_accept 34 35 261 (accept_3_4 34 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 261 (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 35 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 261 (accept_3_4 31 35 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 261 (accept_3_4 28 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 261 (accept_3_4 25 35 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 35 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 261
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 261 (accept_3_4 22 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 261 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 261 (accept_3_4 19 35 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 261
  (Polychromatic418967fa.accept_19_17_16_14_1_10604 17 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 35 261 (accept_3_4 16 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 35 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 35 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 261 (accept_3_4 13 35 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 261 (Polychromatic418967fa.accept_14_12_7_9_1_726
  12 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 261
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 261 (accept_3_4 10 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 261 (accept_3_4 7 35 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 261
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 261 (accept_3_4 4 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  261 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 35 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 35 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 261 (accept_3_4 1 35 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 35 261))))))))))))))))))))))))))))))))))) (allB_succ 34 261 (allA_succ_of_accept 33 34
  261 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 34 261 (accept_3_5 32 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 34 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 261 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 34 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 261 (accept_3_5 29 34 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 261 (Polychromatic418967fa.accept_15_13_4_6_1_3046
  28 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 261 (accept_3_5 26 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 34 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 261 (accept_3_5 23 34 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 34 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 261
  (Polychromatic418967fa.accept_25_21_9_11_1_15895 21 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 34 261 (accept_3_5 20 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 34 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 34 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 261 (accept_3_5 17 34 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 261
  (Polychromatic418967fa.accept_21_16_13_9_1_2539 16 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 34 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 261 (accept_3_5 14 34 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 34 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 261 (Polychromatic418967fa.accept_13_12_8_1_1_825
  12 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 261 (accept_3_5 11
  34 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 10 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 34 261 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 34 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 261 (accept_3_5 8 34 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 34 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 261 (Polychromatic418967fa.accept_12_6_10_9_1_531 6
  34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 261 (accept_3_5 5 34 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4
  34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 261 (accept_3_5 2 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 261)))))))))))))))))))))))))))))))))) (allB_succ 33 261 (allA_succ_of_accept 32 33 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 33 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 261 3 10 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 261 (Polychromatic418967fa.accept_13_3_7_1_1_334 29
  33 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 33 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 261 3 9 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 261 (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 33 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 33 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 261 3 8 11 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 261
  (Polychromatic418967fa.accept_18_5_15_9_1_1919 23 33 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 22 33 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 261 3 7 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 33 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 261
  (Polychromatic418967fa.accept_13_6_7_1_1_335 19 33 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 261 3 6 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 261 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 33 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 261 3 5 11 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 261
  (Polychromatic418967fa.accept_20_14_13_1_1_8844 14 33 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 261 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 33 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 261 3 4 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 33 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 33 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 261 3 3 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 33 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 261 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 33 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 261 3 2 11 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 261
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 33 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 33 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 261 3 1 11 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 33 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 261
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 33 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 261))))))))))))))))))))))))))))))))) (allB_succ 32 261 (allA_succ_of_accept 31 32 261 (accept_3_4 31 32
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 261
  (Polychromatic418967fa.accept_12_6_8_9_1_553 30 32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 261 (accept_3_4 28 32 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 32 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 26
  32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 261 (accept_3_4 25 32
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 261
  (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 261 (accept_3_4 22 32 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 32 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 20
  32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 261 (accept_3_4 19 32
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 261
  (Polychromatic418967fa.accept_12_6_8_9_1_553 18 32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 32 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 261 (accept_3_4 16 32 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 32 261 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 32 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 261
  (Polychromatic418967fa.accept_17_14_15_6_1_4819 14 32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 261 (accept_3_4 13 32 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 261 (accept_3_4 10 32 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 32 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 261
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 261 (accept_3_4 7 32 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  261 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 261 (accept_3_4 4 32 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 32 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 261 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2
  32 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 261 (accept_3_4 1 32 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 261)))))))))))))))))))))))))))))))) (allB_succ 31 261
  (allA_succ_of_accept 30 31 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 261 (accept_3_5 29 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 27
  31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 261 (accept_3_5 26 31
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 261
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 261 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 261 (accept_3_5 23 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974
  21 31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 261 (accept_3_5 20
  31 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 261 (accept_3_5 17 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 261 (accept_3_5 14 31
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 261 (accept_3_5 11 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9
  31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 261 (accept_3_5 8 31 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 261 (Polychromatic418967fa.accept_15_7_1_6_1_6150 7
  31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 261 (accept_3_5 5 31 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 261 (accept_3_5 2 31 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 31 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 261))))))))))))))))))))))))))))))) (allB_succ 30 261
  (allA_succ_of_accept 29 30 261 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 30 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 30 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 261 3 9 10 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 30 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 261 (Polychromatic418967fa.accept_14_11_2_9_1_5873 25 30 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 261 3 8 10 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 261
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 30 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 261 3 7 10 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 30 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 261 3 6 10 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 261
  (Polychromatic418967fa.accept_18_17_12_9_1_3031 17 30 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 30 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 261 3 5 10 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 30 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 261
  (Polychromatic418967fa.accept_20_13_10_1_1_5903 13 30 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 261 3 4 10 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 30 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 261 3 3 10 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 30 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 261 3 2 10 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 261 (Polychromatic418967fa.accept_13_5_4_1_1_364 5 30 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 30 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 261 3 1 10 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 30 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 261 (Polychromatic418967fa.accept_23_1_7_8_1_9423 1 30 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 261)))))))))))))))))))))))))))))) (allB_succ
  29 261 (allA_succ_of_accept 28 29 261 (accept_3_4 28 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 29 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 261 (accept_3_4 25 29 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 24
  29 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 261
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 23 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 261 (accept_3_4 22 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 261 (Polychromatic418967fa.accept_22_21_7_19_1_9780 21 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 261 (accept_3_4 19 29 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 29 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 261 (accept_3_4 16 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 261 (accept_3_4 13 29 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 29 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 261
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 261 (accept_3_4 10 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 261 (accept_3_4 7 29 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 261 (accept_3_4 4 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 29 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 261 (accept_3_4 1 29 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 261))))))))))))))))))))))))))))) (allB_succ 28 261 (allA_succ_of_accept 27 28 261
  (Polychromatic418967fa.accept_19_8_9_14_1_6364 27 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 261 (accept_3_5 26 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 261 (Polychromatic418967fa.accept_16_8_12_5_1_200 24 28 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 261 (accept_3_5 23 28 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 261 (Polychromatic418967fa.accept_13_9_2_1_1_813 22 28 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 261
  (Polychromatic418967fa.accept_17_4_11_6_1_3730 21 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 261 (accept_3_5 20 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 261 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 261 (accept_3_5 17 28 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 261 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 28 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 261
  (Polychromatic418967fa.accept_18_15_10_9_1_2009 15 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 261 (accept_3_5 14 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 261 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 28 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 261 (accept_3_5 11 28 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 261 (Polychromatic418967fa.accept_16_10_12_5_1_2254 10 28
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 261
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 261 (accept_3_5 8 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 261 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 28 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 261 (accept_3_5 5 28 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 261 (Polychromatic418967fa.accept_15_4_13_6_1_642 4 28 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 3
  28 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 261 (accept_3_5 2 28 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 261))))))))))))))))))))))))))))
  (allB_succ 27 261 (allA_succ_of_accept 26 27 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 27 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 261 3 8 9 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 27 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 261 3 7 9 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 261
  (Polychromatic418967fa.accept_15_5_12_6_1_639 20 27 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 27 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 261 9 2 3 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 27 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 261
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 27 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 261 3 5 9 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 27 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 261 3 4 9 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 261 9 1 3 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 261 3 2 9 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 27 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 27 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 261 3 1 9 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 27 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 261))))))))))))))))))))))))))) (allB_succ 26 261 (allA_succ_of_accept 25
  26 261 (accept_3_4 25 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 261 (accept_3_4 22 26 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 261 (Polychromatic418967fa.accept_14_7_12_9_1_2926 21 26 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 261
  (Polychromatic418967fa.accept_15_5_11_6_1_692 20 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 261 (accept_3_4 19 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 261 (accept_3_4 16 26 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 261
  (Polychromatic418967fa.accept_16_14_10_5_1_1393 14 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 261 (accept_3_4 13 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 261 (accept_3_4 10 26 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 26 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 261
  (Polychromatic418967fa.accept_17_8_9_6_1_7330 8 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 261 (accept_3_4 7 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  261 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 26 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 261 (accept_3_4 4 26 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2
  26 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 261 (accept_3_4 1 26 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 261)))))))))))))))))))))))))) (allB_succ 25 261
  (allA_succ_of_accept 24 25 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 25 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 261 (accept_3_5 23 25 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662
  21 25 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 261 (accept_3_5 20
  25 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 25 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 261 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 25 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 261 (accept_3_5 17 25 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 261 (Polychromatic418967fa.accept_12_3_1_9_1_202
  15 25 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 261 (accept_3_5 14
  25 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 25 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 261 (accept_3_5 11 25 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 25 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 25 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9
  25 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 261 (accept_3_5 8 25 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 261 (Polychromatic418967fa.accept_19_7_6_14_1_11872
  7 25 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 25 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 261 (accept_3_5 5 25 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 25 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 261 (accept_3_5 2 25 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 261 (Polychromatic418967fa.accept_15_1_10_6_1_631 1 25 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 261))))))))))))))))))))))))) (allB_succ 24 261
  (allA_succ_of_accept 23 24 261 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 24 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 24 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 261 3 7 8 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 24 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 24 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 261 3 6 8 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 24 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 261
  (Polychromatic418967fa.accept_11_5_2_8_1_866 16 24 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 261 3 5 8 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 261 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 24 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 24 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 261 3 4 8 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 261
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 24 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 261 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 24 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 261 3 3 8 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 24 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 261
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 24 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 261 3 2 8 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 261 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 24 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 261 3 1 8 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 261
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 24 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 261)))))))))))))))))))))))) (allB_succ 23 261 (allA_succ_of_accept 22 23
  261 (accept_3_4 22 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 261
  (Polychromatic418967fa.accept_19_2_4_14_1_10629 21 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 261 (accept_3_4 19 23 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 261 (Polychromatic418967fa.accept_13_4_10_1_1_1390
  17 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 261 (accept_3_4 16
  23 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 261
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 261 (accept_3_4 13 23 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 23 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 261
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 261 (accept_3_4 10 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 261 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 261 (accept_3_4 7 23 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 261
  (Polychromatic418967fa.accept_20_5_3_1_1_10415 5 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 261 (accept_3_4 4 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  261 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 23 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 23 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 261 (accept_3_4 1 23 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 23 261))))))))))))))))))))))) (allB_succ 22 261 (allA_succ_of_accept 21 22 261
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 22 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 261 (accept_3_5 20 22 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 261 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 22 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 261 (accept_3_5 17 22 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 22 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 261 (accept_3_5 14 22 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 261 (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 22 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 261 (accept_3_5 11 22 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 22 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 261
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 22 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 261 (accept_3_5 8 22 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 22 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 261 (accept_3_5 5 22 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 261 (Polychromatic418967fa.accept_16_4_6_5_1_2245 4 22 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 261 (accept_3_5 2 22 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 261)))))))))))))))))))))) (allB_succ 21
  261 (allA_succ_of_accept 20 21 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 21 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 261 (Polychromatic418967fa.accept_13_6_8_1_1_2913
  19 21 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 261 3 6 7 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 261
  (Polychromatic418967fa.accept_19_17_2_14_1_11897 17 21 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 261 (Polychromatic418967fa.accept_14_2_7_9_1_2937 16 21 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 261 3 5 7 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 261 (Polychromatic418967fa.accept_18_14_3_9_1_4234
  14 21 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 261
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 21 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 261 3 4 7 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 261 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 21 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 261 (Polychromatic418967fa.accept_17_10_4_6_1_3757 10 21
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 261 3 3 7 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 261
  (Polychromatic418967fa.accept_18_8_3_9_1_4232 8 21 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 261 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 21 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 261 3 2 7 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 261 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 21 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 261
  (Polychromatic418967fa.accept_19_4_2_14_1_10651 4 21 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 261 3 1 7 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 261 (Polychromatic418967fa.accept_14_2_7_9_1_2937 2 21 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 261 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 21 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 261))))))))))))))))))))) (allB_succ 20 261
  (allA_succ_of_accept 19 20 261 (accept_3_4 19 20 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 20 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 261 (accept_3_4 16 20 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 20 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 261
  (Polychromatic418967fa.accept_15_14_5_6_1_6168 14 20 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 261 (accept_3_4 13 20 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 261 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 20 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 261 (accept_3_4 10 20 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 20 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 20 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 261 (accept_3_4 7 20 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  261 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 20 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 261 (accept_3_4 4 20 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 20 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 261 (Polychromatic418967fa.accept_19_2_1_14_1_3663
  2 20 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 261 (accept_3_4 1 20
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 261)))))))))))))))))))) (allB_succ 19 261
  (allA_succ_of_accept 18 19 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 261 (accept_3_5 17 19 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 19 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 261 (Polychromatic418967fa.accept_10_5_9_1_1_187
  15 19 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 261 (accept_3_5 14
  19 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 261
  (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 19 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 19 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 19 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 261 (accept_3_5 11 19 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 19 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9
  19 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 261 (accept_3_5 8 19 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 261 (Polychromatic418967fa.accept_13_7_6_1_1_368 7
  19 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 261 (accept_3_5 5 19 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 19 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 261 (accept_3_5 2 19 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 261 (Polychromatic418967fa.accept_17_1_2_6_1_818 1 19 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 261))))))))))))))))))) (allB_succ 18 261 (allA_succ_of_accept 17
  18 261 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 18 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 18 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 261 3 5 6 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  18 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 18 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 261 3 4 6 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 18 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 261 9 1 2 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 18 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 261 3 2 6 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 261
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 18 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 261 3 1 6 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 18 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 261 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 18 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 261)))))))))))))))))) (allB_succ 17 261
  (allA_succ_of_accept 16 17 261 (accept_3_4 16 17 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 17 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 261 (accept_3_4 13 17 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 261
  (Polychromatic418967fa.accept_15_11_2_6_1_3010 11 17 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 261 (accept_3_4 10 17 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 261 (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 17 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 261 (accept_3_4 7 17 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 261 (accept_3_4 4 17 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  261 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 17 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 261 (accept_3_4 1 17 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 261))))))))))))))))) (allB_succ 16 261 (allA_succ_of_accept 15 16 261
  (Polychromatic418967fa.accept_10_5_6_1_1_836 15 16 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 261 (accept_3_5 14 16 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 16 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 261 (accept_3_5 11 16 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 261 (Polychromatic418967fa.accept_15_10_1_6_1_3033 10 16 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 261
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 16 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 261 (accept_3_5 8 16 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 261 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 16 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 261 (accept_3_5 5 16 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 261 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 16 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 3
  16 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 261 (accept_3_5 2 16 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 261)))))))))))))))) (allB_succ 15 261
  (allA_succ_of_accept 14 15 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 15 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 261 3 4 5 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 15 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 261 3 3 5 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 261 (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 15 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 261
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 15 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 261 3 2 5 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 15 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 15 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 261 3 1 5 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 15 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 261))))))))))))))) (allB_succ 14 261 (allA_succ_of_accept 13 14 261
  (accept_3_4 13 14 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 261
  (Polychromatic418967fa.accept_25_12_14_11_1_14153 12 14 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 14 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 261 (accept_3_4 10 14 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 14 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 261
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 8 14 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 14 261 (accept_3_4 7 14 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14
  261 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 14 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 261 (accept_3_4 4 14 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 261 (Polychromatic418967fa.accept_21_2_14_9_1_3866
  2 14 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 261 (accept_3_4 1 14
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 261)))))))))))))) (allB_succ 13 261 (allA_succ_of_accept 12
  13 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 13 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 261 (accept_3_5 11 13 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 261 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 13 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 261 (accept_3_5 8 13 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 261 (Polychromatic418967fa.accept_15_7_13_6_1_696 7
  13 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 261
  (Polychromatic418967fa.accept_18_6_13_9_1_4218 6 13 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 261 (accept_3_5 5 13 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 13 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 261 (accept_3_5 2 13 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 261))))))))))))) (allB_succ 12 261 (allA_succ_of_accept 11 12
  261 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 12 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 261 3 3 4 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 12 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 261
  (Polychromatic418967fa.accept_14_7_12_9_1_2926 7 12 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 261 3 2 4 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 261 (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 12 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 12 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 261 3 1 4 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 261
  (Polychromatic418967fa.accept_13_2_12_1_1_343 2 12 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 12 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 261)))))))))))) (allB_succ 11 261 (allA_succ_of_accept 10 11 261
  (accept_3_4 10 11 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 261
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 11 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 261 (accept_3_4 7 11 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  11 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 261 (accept_3_4 4 11 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 3
  11 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 261 (accept_3_4 1 11 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  261))))))))))) (allB_succ 10 261 (allA_succ_of_accept 9 10 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 10 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 261 (accept_3_5 8 10 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 10 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 261 (accept_3_5 5 10 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  261 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 10 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 261 (accept_3_5 2 10 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 261)))))))))) (allB_succ 9 261 (allA_succ_of_accept 8
  9 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 9 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 9 261 (Polychromatic418967fa.accept_23_7_9_8_1_9513 7 9 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 261 3 2 3 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 9
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 9 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 261 3 1 3 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 9 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 261 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 9 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 261))))))))) (allB_succ 8 261
  (allA_succ_of_accept 7 8 261 (accept_3_4 7 8 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 8 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 261 (accept_3_4 4 8 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 261 (Polychromatic418967fa.accept_15_2_8_6_1_1340 2
  8 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 261 (accept_3_4 1 8 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 261)))))))) (allB_succ 7 261 (allA_succ_of_accept 6 7 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 261 (accept_3_5 5 7 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 261
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 7 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 261 (accept_3_5 2 7 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 261 (Polychromatic418967fa.accept_15_1_7_6_1_6127 1 7 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 261))))))) (allB_succ 6 261 (allA_succ_of_accept 5 6 261
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 6 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 6 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 261 3 1 2 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 6 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 6 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 261)))))) (allB_succ 5 261 (allA_succ_of_accept 4 5 261 (accept_3_4 4 5 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 5 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 261 (accept_3_4 1 5 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 261))))) (allB_succ 4 261 (allA_succ_of_accept 3 4 261
  (Polychromatic418967fa.accept_13_3_4_1_1_363 3 4 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 261 (accept_3_5 2 4 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 261
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 261)))) (allB_succ 3 261 (allA_succ_of_accept 2 3 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 3 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 261))) (allB_succ 2 261 (allA_succ_of_accept 1 2 261 (accept_3_4 1 2 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 261)) (allB_two
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


