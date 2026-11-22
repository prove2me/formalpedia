-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch285_Segment000
-- name    : Polychromatic418967fa_Branch285_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:53:27.364369+00:00
-- url     : https://prove2.me/theorems/bc6eea6d-09a4-471d-9456-5dad3753205f
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

def Polychromatic418967fa.branch_285_segment_000 : allB 100 285 :=
  allB_succ 99 285 (allA_succ_of_accept 98 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 97 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 285 3 32 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 285 3 31 33 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 285
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 92 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 285 3 30 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 89
  99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 88 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 285 3 29 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 85 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 285 3 28 33 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 83 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 285 3 27 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 80
  99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 285
  (Polychromatic418967fa.accept_12_7_3_9_1_999 79 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 285 3 26 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 285 3 25 33 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 285 3 24 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 71
  99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 285 3 23 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 285 (Polychromatic418967fa.accept_21_5_15_12_1_5519 68 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 285 3 22 33 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 285
  (Polychromatic418967fa.accept_12_5_3_9_1_541 65 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 285 3 21 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 285
  (Polychromatic418967fa.accept_10_1_9_5_1_83 61 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 285 3 20 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 285 3 19 33 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 285
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 285 3 18 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 53
  99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 52 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 285 3 17 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 285 3 16 33 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 285
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 285 3 15 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 44
  99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 285
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 285 3 14 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 285 (Polychromatic418967fa.accept_13_1_8_12_1_2045 40 99
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 285 3 13 33 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 285 3 12 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 285 3 11 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 285 3 10 33 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 285
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 285 (Polychromatic418967fa.accept_18_10_9_15_1_7267 28 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 285 3 9 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 285 3 8 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 285 3 7 33 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 285 3 6 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 285
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 285 3 5 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 285 3 4 33 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 285 3 3 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 285 (Polychromatic418967fa.accept_16_8_3_13_1_7295 8 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 285
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 285 3 2 33 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 99 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 285 3 1 33 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  285 (allA_succ_of_accept 97 98 285 (accept_3_4 97 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 285 (Polychromatic418967fa.accept_13_5_7_12_1_2757 96 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 285 (accept_3_4 94 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 93 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 92 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 285 (accept_3_4 91 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 90 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 285 (accept_3_4 88 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 86 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 285 (accept_3_4 85 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 84 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 285 (accept_3_4 82 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 285 (Polychromatic418967fa.accept_21_18_14_12_1_4075 81 98 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 285
  (Polychromatic418967fa.accept_22_14_10_21_1_8310 80 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 98 285 (accept_3_4 79 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 98 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 98 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 98 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 98 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 285 (accept_3_4 76 98 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 75
  98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 285 (accept_3_4 73 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 285 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 285 (accept_3_4 70 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 285 (Polychromatic418967fa.accept_13_4_7_12_1_2823 69 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 285 (accept_3_4 67 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 285 (accept_3_4 64 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 285
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 285 (accept_3_4 61 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 285 (Polychromatic418967fa.accept_13_8_7_12_1_3637 60 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 285 (accept_3_4 58 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 285 (accept_3_4 55 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 285 (accept_3_4 52 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 285 (accept_3_4 49 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 285 (accept_3_4 46 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 285 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 285
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 44 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 285 (accept_3_4 43 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 285 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 285 (accept_3_4 40 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 285 (accept_3_4 37 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 285 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 285 (accept_3_4 34 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 285 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 285 (accept_3_4 31 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 285 (accept_3_4 28 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 285
  (Polychromatic418967fa.accept_21_5_14_12_1_8720 26 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 285 (accept_3_4 25 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 285 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 285 (accept_3_4 22 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 285 (accept_3_4 19 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 285 (accept_3_4 16 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 285 (accept_3_4 13 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 285 (accept_3_4 10 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 285 (Polychromatic418967fa.accept_22_9_10_21_1_12997 9 98 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 285
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 8 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 285 (accept_3_4 7 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  285 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 98 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 285 (accept_3_4 4 98 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 98
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 285 (accept_3_4 1 98 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  285 (allA_succ_of_accept 96 97 285 (Polychromatic418967fa.accept_11_8_9_10_1_503 96 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 285 (accept_3_5 95 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 93 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 97 285 (accept_3_5 92 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  97 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 91 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 97 285 (Polychromatic418967fa.accept_14_6_13_5_1_534 90 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 285 (accept_3_5 89 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 285
  (Polychromatic418967fa.accept_12_3_1_9_1_202 87 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 97 285 (accept_3_5 86 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  97 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 85 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 97 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 285 (accept_3_5 83 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 81 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 285 (accept_3_5 80 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 285 (Polychromatic418967fa.accept_17_11_12_13_1_3030 79 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 285 (accept_3_5 77 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 75 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 285 (accept_3_5 74 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 285 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 285 (accept_3_5 71 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 285
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 69 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 285 (accept_3_5 68 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 66 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 285 (accept_3_5 65 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 285
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 285 (accept_3_5 62 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 285 (Polychromatic418967fa.accept_24_13_1_21_1_10818 61 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 285 (accept_3_5 59 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 285 (accept_3_5 56 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 285 (Polychromatic418967fa.accept_13_2_6_12_1_1334 54 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 285 (accept_3_5 53 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 285
  (Polychromatic418967fa.accept_12_3_1_9_1_202 51 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 285 (accept_3_5 50 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 285 (accept_3_5 47 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 285
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 285 (accept_3_5 44 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 285 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 285 (accept_3_5 41 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 285 (accept_3_5 38 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 285 (accept_3_5 35 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 285
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 285 (accept_3_5 32 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 285 (accept_3_5 29 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 285
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 285 (accept_3_5 26 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 285 (Polychromatic418967fa.accept_21_3_13_12_1_2653 24 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 285 (accept_3_5 23 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 97 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 285 (accept_3_5 20 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 285 (accept_3_5 17 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 285 (accept_3_5 14 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 285 (accept_3_5 11 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 285
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 285 (accept_3_5 8 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  285 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 285 (Polychromatic418967fa.accept_14_6_13_5_1_534 6 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 285 (accept_3_5 5 97 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 285 (accept_3_5 2 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  285 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 96 285 (allA_succ_of_accept 95 96 285 (Polychromatic418967fa.accept_13_4_5_12_1_751 95 96 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 285
  (Polychromatic418967fa.accept_10_4_6_5_1_74 94 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 96 285 3 31 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 92 96 285 (Polychromatic418967fa.accept_13_1_5_12_1_306 92 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 285 (Polychromatic418967fa.accept_10_1_6_5_1_304 91 96 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 285 3 30 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 285
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 89 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 285 (Polychromatic418967fa.accept_18_16_6_15_1_3376 88 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 96 285 3 29 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 96 285 (Polychromatic418967fa.accept_11_9_8_10_1_934
  86 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 285
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 85 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 285 3 28 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 285 (Polychromatic418967fa.accept_17_15_11_13_1_2039 83 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 96 285 (Polychromatic418967fa.accept_13_4_5_12_1_751 82 96 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 285 3 27 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 285
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 80 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 96 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 79 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 285 3 26 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 285 (Polychromatic418967fa.accept_14_7_12_5_1_1861
  77 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 285
  (Polychromatic418967fa.accept_18_4_6_15_1_2250 76 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 96 285 3 25 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 96 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 74 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 285 (Polychromatic418967fa.accept_13_8_5_12_1_2755 73 96
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 285 3 24 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 285
  (Polychromatic418967fa.accept_10_1_6_5_1_304 71 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 285 (Polychromatic418967fa.accept_18_16_6_15_1_3376 70 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 96 285 3 23 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 96 285 (Polychromatic418967fa.accept_22_2_8_21_1_16092
  68 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 285
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 67 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 285 3 22 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 285 (Polychromatic418967fa.accept_18_11_6_15_1_5953 65 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 96 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 285 3 21 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 285
  (Polychromatic418967fa.accept_23_16_4_9_1_17439 62 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 285 (Polychromatic418967fa.accept_10_1_6_5_1_304 61 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 285 3 20 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  59 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 285
  (Polychromatic418967fa.accept_13_6_5_12_1_307 58 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 96 285 3 19 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 96 285 (Polychromatic418967fa.accept_13_4_5_12_1_751 56 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 285 (Polychromatic418967fa.accept_20_15_16_5_1_7771 55 96
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 285 3 18 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 285
  (Polychromatic418967fa.accept_11_9_8_10_1_934 53 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 285 (Polychromatic418967fa.accept_14_10_12_5_1_3466 52 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 96 285 3 17 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 96 285 (Polychromatic418967fa.accept_20_10_16_5_1_3311
  50 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 285
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 285 3 16 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 285 (Polychromatic418967fa.accept_13_8_5_12_1_2755 47 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 285 (Polychromatic418967fa.accept_13_7_5_12_1_1305 46 96
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 285 3 15 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 285
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 285 (Polychromatic418967fa.accept_13_4_5_12_1_751 43 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 285 3 14 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 285 (Polychromatic418967fa.accept_10_1_6_5_1_304 41
  96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 285
  (Polychromatic418967fa.accept_13_1_5_12_1_306 40 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 96 285 3 13 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 96 285 (Polychromatic418967fa.accept_14_10_12_5_1_3466 38 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 285 (Polychromatic418967fa.accept_25_12_21_10_1_14119 37 96
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 285 3 12 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 285
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 35 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 96 285 3 11 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 96 285 (Polychromatic418967fa.accept_13_6_5_12_1_307
  32 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 285
  (Polychromatic418967fa.accept_10_1_6_5_1_304 31 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 285 3 10 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 29 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 285 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 96
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 285 3 9 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 285
  (Polychromatic418967fa.accept_22_4_8_21_1_17438 26 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 285 (Polychromatic418967fa.accept_23_2_4_9_1_14298 25 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 285 3 8 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 285 (Polychromatic418967fa.accept_17_6_11_13_1_4180 23 96
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 285
  (Polychromatic418967fa.accept_18_4_6_15_1_2250 22 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 96 285 3 7 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 96 285 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 96 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 285 3 6 32 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 285
  (Polychromatic418967fa.accept_13_4_5_12_1_751 17 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 285 (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 285 3 5 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 96 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 285
  (Polychromatic418967fa.accept_22_13_8_21_1_9872 13 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 285 3 4 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 285 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 285 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 96
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 285 3 3 32 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 285
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 285 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 285 3 2 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 285 (Polychromatic418967fa.accept_18_5_6_15_1_3413 5 96 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 285
  (Polychromatic418967fa.accept_10_4_6_5_1_74 4 96 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 96 285 3 1 32 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 96 285 (Polychromatic418967fa.accept_13_2_5_12_1_2043 2 96 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 285 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 96 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 285
  (allA_succ_of_accept 94 95 285 (accept_3_4 94 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 285 (accept_3_4 91 95 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 90 95 285 5 18 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 95 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 89 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 95 285 (accept_3_4 88 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 95 285 (Polychromatic418967fa.accept_12_3_11_9_1_193
  87 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 95 285 5 17 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 95 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 83 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 285 (accept_3_4 82 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 285 (Polychromatic418967fa.accept_13_3_4_12_1_36
  81 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 95 285 5 16 19 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 95 285 (accept_3_4 79
  95 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 95 285 (Polychromatic418967fa.accept_17_9_10_13_1_6698 77 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 95 285 19 4 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 95 285 5 15 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 95 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 285 (accept_3_4 73 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 72
  95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 95 285 5 14 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 95 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 285 (accept_3_4 67 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 95 285 5 13 19 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 95 285 (accept_3_4 64
  95 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 285
  (Polychromatic418967fa.accept_12_3_11_9_1_193 63 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 285 (accept_3_4 61 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 95 285 5 12 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 95 285 (Polychromatic418967fa.accept_13_7_4_12_1_1341 59 95 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 285 (accept_3_4 58 95 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 95 285 19 3 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 95 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 95 285 5 11 19 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 95 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 95 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 285 (accept_3_4 52 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 95 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 95 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 285 5 10 19 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 285 (accept_3_4 49 95 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 285 (accept_3_4 46 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 95
  285 5 9 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  95 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 95 285 (accept_3_4 43 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 95 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 95 285 5 8 19 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 95 285
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 95 285 19 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 95 285 (accept_3_4 37 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 95 285 5 7 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 95 285 (accept_3_4 34 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 95 285 (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 285 (accept_3_4 31 95 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 95 285 5 6 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 95 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 285 (accept_3_4 28 95
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 95 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 95 285 5 5 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 95 285 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 95
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 285 (accept_3_4 22 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 95 285 5 4 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 19 95 285 19 1 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 18 95 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 285 (accept_3_4 16 95
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 95 285 5 3 19 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 95 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 285 (accept_3_4 13 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 95 285 5 2 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 95 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 95
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 285 (accept_3_4 7 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 95 285 5 1 19 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 95 285 (accept_3_4 4 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  285 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 95 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 285 (accept_3_4 1 95 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 285
  (allA_succ_of_accept 93 94 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 93 94 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 285 (accept_3_5 92 94 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 285 (Polychromatic418967fa.accept_12_6_10_9_1_531
  90 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 285 (accept_3_5 89
  94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 285
  (Polychromatic418967fa.accept_9_7_4_6_1_273 88 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 285 (accept_3_5 86 94 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 84
  94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 285 (accept_3_5 83 94
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 285 (Polychromatic418967fa.accept_9_1_4_6_1_5
  82 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 285
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 285 (accept_3_5 80 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 285 (accept_3_5 77 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 76 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 285 (accept_3_5 74 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 285 (accept_3_5 71 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 285
  (Polychromatic418967fa.accept_10_9_4_5_1_616 69 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 285 (accept_3_5 68 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 285 (accept_3_5 65 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 285 (accept_3_5 62 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 285 (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 285 (accept_3_5 59 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 94 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 285 (accept_3_5 56 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 285 (accept_3_5 53 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 285 (accept_3_5 50 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 285 (accept_3_5 47 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 285
  (Polychromatic418967fa.accept_18_9_4_15_1_555 45 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 285 (accept_3_5 44 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 285 (accept_3_5 41 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 285 (Polychromatic418967fa.accept_14_12_10_5_1_2712 40 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 285 (accept_3_5 38 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 285 (accept_3_5 35 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 285
  (Polychromatic418967fa.accept_16_1_14_13_1_3834 33 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 285 (accept_3_5 32 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 285 (accept_3_5 29 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 285 (accept_3_5 26 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 285 (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 285 (accept_3_5 23 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 94 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 285 (accept_3_5 20 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 285 (accept_3_5 17 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 285 (accept_3_5 14 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 285 (accept_3_5 11 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 94 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 285 (accept_3_5 8 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 94 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 285 (accept_3_5 5 94 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 285 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 94 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 285 (accept_3_5 2 94 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 285
  (allA_succ_of_accept 92 93 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 92 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 91 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 285 3 30 31 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 89 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 285 3 29 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 86
  93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 85 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 285 3 28 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 285 3 27 31 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 285 3 26 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 285 3 25 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 74 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 285 3 24 31 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 285 3 23 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 67 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 285 3 22 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 285 3 21 31 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 285 3 20 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 59
  93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 285 3 19 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 285 3 18 31 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 285 3 17 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 285 3 16 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 285 3 15 31 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 285 3 14 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 285 3 13 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 285 3 12 31 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 285 3 11 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 32
  93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 285 3 10 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 285 3 9 31 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 285 3 8 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 285 3 7 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 285 3 6 31 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 285 3 5 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 285 3 4 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 285 3 3 31 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 285 3 2 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 93 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 285 3 1 31 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 93 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 285
  (allA_succ_of_accept 91 92 285 (accept_3_4 91 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 285 (accept_3_4 88 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 86 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 285 (accept_3_4 85 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 285 (accept_3_4 82 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 285 (accept_3_4 79 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 78 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 285 (accept_3_4 76 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 285 (accept_3_4 73 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 285 (Polychromatic418967fa.accept_16_8_12_13_1_3851 72 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 285 (accept_3_4 70 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 68 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 285 (accept_3_4 67 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 285 (accept_3_4 64 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 285 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 285 (accept_3_4 61 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 285 (accept_3_4 58 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 285
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 56 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 285 (accept_3_4 55 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 285 (accept_3_4 52 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 285 (Polychromatic418967fa.accept_21_9_8_12_1_10321 51 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 285 (accept_3_4 49 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 285 (accept_3_4 46 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 285 (accept_3_4 43 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 285 (accept_3_4 40 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 285 (accept_3_4 37 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 285 (Polychromatic418967fa.accept_16_4_12_13_1_990 36 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 285 (accept_3_4 34 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 285 (accept_3_4 31 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 285 (accept_3_4 28 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 285 (accept_3_4 25 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 285 (accept_3_4 22 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 285 (accept_3_4 19 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 285 (accept_3_4 16 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 285 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 285 (accept_3_4 13 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 285 (accept_3_4 10 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 92 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 285 (accept_3_4 7 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 285 (accept_3_4 4 92 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 92 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 285 (Polychromatic418967fa.accept_13_2_1_12_1_1326
  2 92 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 285 (accept_3_4 1 92
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 285
  (allA_succ_of_accept 90 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 285 (accept_3_5 89 91 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 285 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  87 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 285 (accept_3_5 86
  91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 285
  (Polychromatic418967fa.accept_9_4_1_6_1_284 85 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 91 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 285 (accept_3_5 83 91 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 285
  (Polychromatic418967fa.accept_21_18_7_12_1_10175 81 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 91 285 (accept_3_5 80 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 91 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 79 91 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 285 (accept_3_5 77 91 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 91 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 76
  91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 75 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 285 (accept_3_5 74 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 73 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 285 (Polychromatic418967fa.accept_14_2_7_5_1_5450 72 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 285 (accept_3_5 71 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 285
  (Polychromatic418967fa.accept_10_9_1_5_1_594 69 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 285 (accept_3_5 68 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 285 (accept_3_5 65 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 285
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 285 (accept_3_5 62 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 285 (Polychromatic418967fa.accept_21_18_7_12_1_10175 60 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 285 (accept_3_5 59 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 285 (accept_3_5 56 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 285 (Polychromatic418967fa.accept_20_15_11_5_1_7737 55 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 285 (accept_3_5 53 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 285
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 285 (accept_3_5 50 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 285 (accept_3_5 47 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 285
  (Polychromatic418967fa.accept_17_11_6_13_1_10553 45 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 91 285 (accept_3_5 44 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 91 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 91 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 285 (accept_3_5 41 91 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 40
  91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 285 (accept_3_5 38 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 285 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 285 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 285 (accept_3_5 35 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 285
  (Polychromatic418967fa.accept_22_11_3_21_1_17437 33 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 91 285 (accept_3_5 32 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 91 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 91 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 285 (accept_3_5 29 91 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 285
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 285 (accept_3_5 26 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 285 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 285 (accept_3_5 23 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 285 (accept_3_5 20 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 285 (accept_3_5 17 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 285
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 285 (accept_3_5 14 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 285 (accept_3_5 11 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 285
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 285 (accept_3_5 8 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  285 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 285 (accept_3_5 5 91 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 285 (accept_3_5 2 91 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 285 (Polychromatic418967fa.accept_21_1_7_12_1_1465
  1 91 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 285
  (allA_succ_of_accept 89 90 285 (Polychromatic418967fa.accept_11_1_2_10_1_1426 89 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 285 3 29 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 285
  (Polychromatic418967fa.accept_12_2_6_9_1_19 86 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 90 285 5 17 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 90 285 3 28 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 285 (Polychromatic418967fa.accept_12_10_6_9_1_549 82 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 90 285 3 27 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 90 285 5 16 18 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 285 3 26 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 90 285 (Polychromatic418967fa.accept_17_9_5_13_1_2033 77 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 285 15 5 6 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 74 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 90 285 (Polychromatic418967fa.accept_20_13_10_5_1_3338 73 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 285 3 24 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 285 5 14 18 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 90 285 3 23 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 285
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 285 3 22 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 90 285 5 13 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 90 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 64
  90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 90 285 3 21 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 90 285
  (Polychromatic418967fa.accept_12_2_6_9_1_19 62 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 90 285 (Polychromatic418967fa.accept_17_10_5_13_1_12853 61 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 285 15 4 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 285
  (Polychromatic418967fa.accept_12_10_6_9_1_549 58 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 90 285 3 19 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 90 285 (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 90 285 5 11 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 285 3 18 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 53
  90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 285
  (Polychromatic418967fa.accept_12_4_6_9_1_548 52 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 90 285 3 17 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 90 285 5 10 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 285 (Polychromatic418967fa.accept_17_15_5_13_1_6626 49 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 285 3 16 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 46 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 285 15 3 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 285 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 285 3 14 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 285
  (Polychromatic418967fa.accept_14_13_6_5_1_1853 41 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 90 285 5 8 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 90 285 3 13 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 90 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 285 (Polychromatic418967fa.accept_16_5_10_13_1_6042 37 90
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 285 3 12 30 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 285 5 7 18 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 90 285
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 90 285 3 11 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 90 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 285 15 2 6 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 90 285 3 9 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 90 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 90 285 5 5 18 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 285 3 8 30 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 285 3 7 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 285 5 4 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 285 3 6 30 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 285
  (Polychromatic418967fa.accept_20_17_10_5_1_7765 17 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 285 15 1 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 285
  (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 285 3 4 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 285 5 2 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 285 3 3 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 90 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 285 3 2 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 90 285 5 1 18 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 90 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 90 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 285 3 1 30 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 90 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 90 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 285 (allA_succ_of_accept 88 89 285 (accept_3_4 88 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 87 89 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 89 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 285 (accept_3_4 85 89 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 84
  89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 83 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 285 (accept_3_4 82 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 285 (accept_3_4 79 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 285 (Polychromatic418967fa.accept_18_6_17_15_1_4603 78 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 285 (accept_3_4 76 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 285 (accept_3_4 73 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 285 (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 285
  (Polychromatic418967fa.accept_10_1_9_5_1_83 71 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 285 (accept_3_4 70 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 285 (Polychromatic418967fa.accept_13_4_11_12_1_1318 69 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 285 (accept_3_4 67 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 285 (accept_3_4 64 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 285 (accept_3_4 61 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 285 (accept_3_4 58 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 285 (accept_3_4 55 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 285
  (Polychromatic418967fa.accept_11_9_1_10_1_920 53 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 285 (accept_3_4 52 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 285 (accept_3_4 49 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 285 (accept_3_4 46 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 285 (Polychromatic418967fa.accept_18_9_17_15_1_2267 45 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 285 (accept_3_4 43 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 285 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 285 (accept_3_4 40 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 285 (accept_3_4 37 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 285
  (Polychromatic418967fa.accept_11_2_1_10_1_196 35 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 285 (accept_3_4 34 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 285 (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 285 (accept_3_4 31 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 285 (accept_3_4 28 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 285 (accept_3_4 25 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 285 (accept_3_4 22 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 285 (accept_3_4 19 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 285 (Polychromatic418967fa.accept_21_18_5_12_1_4032 18 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 285
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 285 (accept_3_4 16 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 285 (accept_3_4 13 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 285 (accept_3_4 10 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 285 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 285 (accept_3_4 7 89 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 285 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 89 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 285 (accept_3_4 4 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  285 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 89 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 285 (accept_3_4 1 89 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 285 (allA_succ_of_accept 87 88 285 (Polychromatic418967fa.accept_10_7_8_5_1_1008 87 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 285 (accept_3_5 86 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 84 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 88 285 (accept_3_5 83 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  88 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 82 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 88 285 (Polychromatic418967fa.accept_18_9_16_15_1_2241 81 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 285 (accept_3_5 80 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 78 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 285 (accept_3_5 77 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 285 (accept_3_5 74 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 285 (accept_3_5 71 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 285 (Polychromatic418967fa.accept_20_10_8_5_1_7735 70 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 285 (accept_3_5 68 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 285 (accept_3_5 65 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 285 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 285 (accept_3_5 62 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 285
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 60 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 285 (accept_3_5 59 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 285 (accept_3_5 56 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 285
  (Polychromatic418967fa.accept_12_6_4_9_1_544 54 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 285 (accept_3_5 53 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 285 (Polychromatic418967fa.accept_10_2_8_5_1_587 52 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 285 (accept_3_5 50 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 285 (accept_3_5 47 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 285 (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 285 (accept_3_5 44 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 285
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 285 (accept_3_5 41 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 285 (accept_3_5 38 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 285 (accept_3_5 35 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 285 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 285 (accept_3_5 32 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 285 (accept_3_5 29 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 285 (accept_3_5 26 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 285
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 88 285 (accept_3_5 23 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 88 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 88 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 285 (accept_3_5 20 88 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 285
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 285 (accept_3_5 17 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 285 (accept_3_5 14 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 285 (accept_3_5 11 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 285 (accept_3_5 8 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 285 (accept_3_5 5 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  285 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 88 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 285 (accept_3_5 2 88 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 285
  (allA_succ_of_accept 86 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 285 3 28 29 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 285
  (Polychromatic418967fa.accept_10_3_7_5_1_288 83 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 285 3 27 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 285 (Polychromatic418967fa.accept_21_17_3_12_1_3986
  80 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 79 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 285 3 26 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 285 (Polychromatic418967fa.accept_21_13_3_12_1_10213 76 87
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 285 3 25 29 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 285 3 24 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 71
  87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 285 3 23 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 285 (Polychromatic418967fa.accept_10_8_7_5_1_602 68 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 67 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 285 3 22 29 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 285 3 21 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 285
  (Polychromatic418967fa.accept_12_1_3_9_1_174 61 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 285 3 20 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 285 3 19 29 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 285
  (Polychromatic418967fa.accept_21_14_3_12_1_10169 56 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 87 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 87 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 285 3 18 29 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 285
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 285 (Polychromatic418967fa.accept_10_2_7_5_1_605 52 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 87 285 3 17 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 285
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 87 285 3 16 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 87 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 285 3 15 29 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 285 3 14 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 285
  (Polychromatic418967fa.accept_14_12_3_5_1_1868 40 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 87 285 3 13 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 285 3 12 29 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 285
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 285 3 11 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 285 (Polychromatic418967fa.accept_10_2_7_5_1_605 32
  87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 285
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 87 285 3 10 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 87 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 285 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 285 3 9 29 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 285 3 8 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 285 3 7 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 285 (Polychromatic418967fa.accept_16_4_7_13_1_2795 20 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 285 3 6 29 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 285
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 285 3 5 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 285
  (Polychromatic418967fa.accept_10_3_7_5_1_288 13 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 285 3 4 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 285 3 3 29 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 285 3 2 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 285
  (Polychromatic418967fa.accept_16_4_7_13_1_2795 4 87 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 285 3 1 29 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 87 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 285
  (allA_succ_of_accept 85 86 285 (accept_3_4 85 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 285 (accept_3_4 82 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 285 (accept_3_4 79 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 285 (Polychromatic418967fa.accept_11_1_9_10_1_184 78 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 285 (accept_3_4 76 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 285 (accept_3_4 73 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 285 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 285 (accept_3_4 70 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 69 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 285
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 68 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 285 (accept_3_4 67 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 285 (accept_3_4 64 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 285 (accept_3_4 61 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 285 (accept_3_4 58 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 285 (accept_3_4 55 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 285 (accept_3_4 52 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 285
  (Polychromatic418967fa.accept_20_10_6_5_1_7776 50 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 285 (accept_3_4 49 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 285 (accept_3_4 46 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 285 (accept_3_4 43 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 285 (accept_3_4 40 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 285 (accept_3_4 37 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 285 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 285 (accept_3_4 34 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 285 (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 285 (accept_3_4 31 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 285 (accept_3_4 28 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 285 (accept_3_4 25 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 285 (accept_3_4 22 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 285 (accept_3_4 19 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 285 (accept_3_4 16 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 285
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 285 (accept_3_4 13 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 285 (accept_3_4 10 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 86 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 285 (accept_3_4 7 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  285 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 285 (accept_3_4 4 86 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  86 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 285 (accept_3_4 1 86 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 285
  (allA_succ_of_accept 84 85 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 84 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 285 (accept_3_5 83 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 81
  85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 85 285 5 16 17 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 85 285
  (Polychromatic418967fa.accept_9_7_4_6_1_273 79 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 285 (Polychromatic418967fa.accept_21_15_1_12_1_10209 78 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 285 (accept_3_5 77 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 85 285 5 15 17 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 85 285 (accept_3_5 74 85 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 85 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 285
  (Polychromatic418967fa.accept_16_8_5_13_1_1021 72 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 285 (accept_3_5 71 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 85
  285 5 14 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  85 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 85 285 (accept_3_5 68 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 85 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 85 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 85 285 5 13 17 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 85 285
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 85 285 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 285 (accept_3_5 62 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 285 5 12 17 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 285 (accept_3_5 59 85 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 85 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 285 (accept_3_5 56 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 85
  285 5 11 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  85 285 (Polychromatic418967fa.accept_24_6_13_21_1_17436 54 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 85 285 (accept_3_5 53 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 85 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 285 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 85 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 85 285 5 10 17 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 85 285
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 285 (accept_3_5 47 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 285 5 9 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 285 (accept_3_5 44 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 85 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 285
  (Polychromatic418967fa.accept_11_9_8_10_1_934 42 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 285 (accept_3_5 41 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 85
  285 5 8 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  85 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 85 285 (accept_3_5 38 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 85 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 285 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 85
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 85 285 5 7 17 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 85 285
  (Polychromatic418967fa.accept_6_4_1_3_1_77 34 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 85 285 (Polychromatic418967fa.accept_16_1_5_13_1_1025 33 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 285 (accept_3_5 32 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 85 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 285 5 6 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 285 (accept_3_5 29 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 285 (accept_3_5 26 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85
  285 5 5 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  85 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 85 285 (accept_3_5 23 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 85 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 85 285 5 4 17 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 85 285
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 285 (accept_3_5 17 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 285 5 3 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 285 (accept_3_5 14 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 285 (accept_3_5 11 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85
  285 5 2 17 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  85 285 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 85 285 (accept_3_5 8 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 85 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 85 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 85 285 5 1 17 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 85 285
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 285 (accept_3_5 2 85 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 285
  (allA_succ_of_accept 83 84 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 285 3 27 28 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 285 3 26 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 84 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 84 285 3 25 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 84 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 285 3 24 28 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 285 3 23 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 285 3 22 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 285 3 21 28 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 84 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 285 3 20 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 84 285 3 19 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 84 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 285 3 18 28 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 285 3 17 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 285
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 285 3 16 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 285 3 15 28 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 285 3 14 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 41
  84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 84 285 3 13 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 84 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 285 3 12 28 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 285 3 11 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 285 3 10 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 285 3 9 28 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 285 3 8 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 285 3 7 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 285 3 6 28 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 285
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 285 3 5 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 285 3 4 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 285 3 3 28 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 285 3 2 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 84 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 84 285 3 1 28 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 84 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 84 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 285
  (allA_succ_of_accept 82 83 285 (accept_3_4 82 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 285 (accept_3_4 79 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 77 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 285 (accept_3_4 76 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 285 (accept_3_4 73 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 285 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 71 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 285 (accept_3_4 70 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 285 (Polychromatic418967fa.accept_13_4_5_12_1_751 69 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 285 (accept_3_4 67 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 285
  (Polychromatic418967fa.accept_16_1_3_13_1_2785 65 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 285 (accept_3_4 64 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 285 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 285 (accept_3_4 61 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 285 (accept_3_4 58 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 285 (accept_3_4 55 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 285 (accept_3_4 52 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 285 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 285 (accept_3_4 49 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 285
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 285 (accept_3_4 46 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 285 (Polychromatic418967fa.accept_13_6_5_12_1_307 45 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 285 (accept_3_4 43 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 285 (accept_3_4 40 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 285 (accept_3_4 37 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 285 (accept_3_4 34 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 285 (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 285 (accept_3_4 31 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 285 (accept_3_4 28 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 285 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 285 (accept_3_4 25 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 285 (Polychromatic418967fa.accept_16_8_3_13_1_7295 24 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 285 (accept_3_4 22 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 285 (accept_3_4 19 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 285 (accept_3_4 16 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 285 (accept_3_4 13 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 285 (accept_3_4 10 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 285 (Polychromatic418967fa.accept_18_9_11_15_1_4616 9 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 285 (accept_3_4 7 83 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 285 (accept_3_4 4 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  285 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 83 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 285 (accept_3_4 1 83 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 285 (allA_succ_of_accept 81 82 285 (Polychromatic418967fa.accept_11_4_5_10_1_926 81 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 285 (accept_3_5 80 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 285
  (Polychromatic418967fa.accept_10_8_2_5_1_596 78 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 82 285 (accept_3_5 77 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  82 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 285 (accept_3_5 74 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 82 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 285
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 72 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 285 (accept_3_5 71 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 285 (Polychromatic418967fa.accept_16_5_2_13_1_1007 69 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 285 (accept_3_5 68 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 285 (accept_3_5 65 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 285 (Polychromatic418967fa.accept_20_4_2_5_1_4607 64 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 285 (accept_3_5 62 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 285
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 285 (accept_3_5 59 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 285 (accept_3_5 56 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 285
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 285 (accept_3_5 53 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 285 (accept_3_5 50 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 285 (accept_3_5 47 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 285 (Polychromatic418967fa.accept_13_7_4_12_1_1341 46 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 285 (Polychromatic418967fa.accept_14_3_12_5_1_153 45 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 285 (accept_3_5 44 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 285
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 285 (accept_3_5 41 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 285 (accept_3_5 38 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 285
  (Polychromatic418967fa.accept_21_15_19_12_1_8682 36 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 82 285 (accept_3_5 35 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 82 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 82 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 285 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 82 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 285 (accept_3_5 32 82 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 285 (accept_3_5 29 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 285 (accept_3_5 26 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 285
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 285 (accept_3_5 23 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 285 (accept_3_5 20 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 285
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 285 (accept_3_5 17 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 285 (accept_3_5 14 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 285 (accept_3_5 11 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 285 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 285 (Polychromatic418967fa.accept_18_9_10_15_1_7254 9 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 285 (accept_3_5 8 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 285
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 285 (accept_3_5 5 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  285 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 82 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 285 (accept_3_5 2 82 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 285
  (allA_succ_of_accept 80 81 285 (Polychromatic418967fa.accept_13_2_3_12_1_735 80 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 285 3 26 27 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 285
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 77 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 285 3 25 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 285 (Polychromatic418967fa.accept_10_4_1_5_1_1018
  74 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 285
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 73 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 285 3 24 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 285 (Polychromatic418967fa.accept_18_16_9_15_1_4614 70 81
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 285 3 23 27 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 285
  (Polychromatic418967fa.accept_8_4_1_5_1_186 68 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 285 (Polychromatic418967fa.accept_13_2_3_12_1_735 67 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 285 3 22 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 65
  81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 64 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 285 3 21 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 285 (Polychromatic418967fa.accept_13_9_3_12_1_2025 61 81
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 285 3 20 27 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 285
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 285 3 19 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 285 (Polychromatic418967fa.accept_10_6_1_5_1_1024
  56 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 285 3 18 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 285 (Polychromatic418967fa.accept_16_5_1_13_1_1053 53 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 285 3 17 27 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 285 3 16 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 285 (Polychromatic418967fa.accept_18_11_9_15_1_5988
  47 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 285
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 46 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 285 3 15 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 285 3 14 27 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 285 (Polychromatic418967fa.accept_18_4_9_15_1_3383 40 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 285 3 13 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 285 (Polychromatic418967fa.accept_11_5_4_10_1_524
  38 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 285 3 12 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 285 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 285 3 11 27 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 285
  (Polychromatic418967fa.accept_21_11_18_12_1_1494 32 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 81 285 (Polychromatic418967fa.accept_28_3_25_5_1_17435 31 81 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 285 3 10 27 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 285 3 9 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 285 (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 285
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 25 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 81 285 3 8 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 81 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 285 3 7 27 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 285 3 6 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 285 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 285 3 5 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 285 (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 285 3 4 27 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 285
  (Polychromatic418967fa.accept_18_11_9_15_1_5988 11 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 285 (Polychromatic418967fa.accept_18_10_9_15_1_7267 10 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 285 3 3 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 285
  (Polychromatic418967fa.accept_21_7_18_12_1_1493 7 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 81 285 3 2 27 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 285 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 81 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 285 3 1 27 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 81 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 81 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 285
  (allA_succ_of_accept 79 80 285 (accept_3_4 79 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 285 (accept_3_4 76 80 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 75 80 285 5 15 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 80 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 74 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 80 285 (accept_3_4 73 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 80 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 72
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 80 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 285 5 14 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 285 (Polychromatic418967fa.accept_13_4_2_12_1_2800 69 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 68 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 80 285 (accept_3_4 67 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 80 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 66
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 80 285 5 13 16 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 80 285 (accept_3_4 64
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 285
  (Polychromatic418967fa.accept_24_15_8_21_1_7258 63 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 80 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 62 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 80 285 (accept_3_4 61 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 80 285 5 12 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 80 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 285 (accept_3_4 58 80 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 80 285 5 11 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 80 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 80 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 285 (accept_3_4 52 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 51
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 285 5 10 16 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 285 (accept_3_4 49
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 80 285
  (Polychromatic418967fa.accept_9_3_8_6_1_80 48 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 80 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 285 (accept_3_4 46 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 80 285 5 9 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 80 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 80 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 80 285 (accept_3_4 43 80 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 80 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 80 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 80 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 285 5 8 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 285 (accept_3_4 37 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 80 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 36
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 80 285 5 7 16 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 80 285 (accept_3_4 34
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 285
  (Polychromatic418967fa.accept_17_16_12_13_1_3070 33 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 80 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 80 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 285 (accept_3_4 31 80 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 285 5 6 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 80 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 285 (accept_3_4 28 80 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 285 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 80
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 285
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 80 285 5 5 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 80 285 (Polychromatic418967fa.accept_21_3_17_12_1_5530 24 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 285 (accept_3_4 22 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 285 5 4 16 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 285 (accept_3_4 19
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 285
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 80 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 285 (accept_3_4 16 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 80 285 5 3 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 80 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 80 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 285 (accept_3_4 13 80 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 80 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 285 5 2 16 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 80 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 285 (accept_3_4 7 80 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 6
  80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 285 5 1 16 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 285 (accept_3_4 4 80
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 285 (Polychromatic418967fa.accept_9_3_8_6_1_80
  3 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 285 (accept_3_4 1 80 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 285
  (allA_succ_of_accept 78 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 285 (accept_3_5 77 79 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 75
  79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 285 (accept_3_5 74 79
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 73 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 285 (Polychromatic418967fa.accept_21_9_16_12_1_4050 72 79 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 285 (accept_3_5 71 79 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 285
  (Polychromatic418967fa.accept_21_6_16_12_1_1490 69 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 79 285 (accept_3_5 68 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  79 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 285 (accept_3_5 65 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 285
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 285 (accept_3_5 62 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 61 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 285 (accept_3_5 59 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 285 (accept_3_5 56 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 285 (accept_3_5 53 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 285
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 285 (accept_3_5 50 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 285 (accept_3_5 47 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 285 (accept_3_5 44 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 285 (Polychromatic418967fa.accept_23_20_10_9_1_17434 43 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 285 (accept_3_5 41 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 285 (accept_3_5 38 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 285 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 285 (accept_3_5 35 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 285
  (Polychromatic418967fa.accept_20_13_19_5_1_1012 33 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 285 (accept_3_5 32 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 285 (accept_3_5 29 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 285
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 285 (accept_3_5 26 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 285 (accept_3_5 23 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 285 (accept_3_5 20 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 285 (accept_3_5 17 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 285
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 285 (accept_3_5 14 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 285 (accept_3_5 11 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 285
  (Polychromatic418967fa.accept_21_9_16_12_1_4050 9 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 285 (accept_3_5 8 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  285 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 285 (accept_3_5 5 79 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  79 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 285 (accept_3_5 2 79 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 79
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 285
  (allA_succ_of_accept 77 78 285 (Polychromatic418967fa.accept_10_7_8_5_1_1008 77 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 285 3 25 26 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 285 3 24 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 285
  (Polychromatic418967fa.accept_12_10_6_9_1_549 70 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 285 3 23 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 285 (Polychromatic418967fa.accept_11_2_1_10_1_196 68 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 285 3 22 26 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 285
  (Polychromatic418967fa.accept_16_1_14_13_1_3834 65 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 285 (Polychromatic418967fa.accept_11_9_1_10_1_920 64 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 285 3 21 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 62
  78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 285
  (Polychromatic418967fa.accept_21_19_15_12_1_5523 61 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 78 285 3 20 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 285
  (Polychromatic418967fa.accept_12_10_6_9_1_549 58 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 78 285 3 19 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 78 285 (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 285 3 18 26 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 78 285 3 17 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 78 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 50
  78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 285
  (Polychromatic418967fa.accept_16_1_14_13_1_3834 49 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 285 3 16 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 285 3 15 26 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 285
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 285 3 14 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 41
  78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 285
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 78 285 3 13 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 78 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 285 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 285 3 12 26 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 78 285 3 11 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 78 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 32
  78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 285 3 10 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 285 (Polychromatic418967fa.accept_18_11_6_15_1_5953 29 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 285 3 9 26 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 285
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 78 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 285 3 8 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 285
  (Polychromatic418967fa.accept_10_2_8_5_1_587 22 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 78 285 3 7 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 78 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 285 3 6 26 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 78 285 3 5 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 78 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 285 3 4 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 285 3 3 26 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 285
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 285 3 2 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 285 (Polychromatic418967fa.accept_17_5_10_13_1_10558 5 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 78 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 78 285 3 1 26 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 78 285 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 78 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 285 (Polychromatic418967fa.accept_16_1_14_13_1_3834 1 78 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 285
  (allA_succ_of_accept 76 77 285 (accept_3_4 76 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 285 (accept_3_4 73 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 285 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 285 (accept_3_4 70 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 285 (Polychromatic418967fa.accept_21_6_14_12_1_4003 69 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 285 (accept_3_4 67 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 285 (accept_3_4 64 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 285 (accept_3_4 61 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 285 (Polychromatic418967fa.accept_18_6_5_15_1_7292 60 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 285
  (Polychromatic418967fa.accept_22_15_11_21_1_17433 59 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 77 285 (accept_3_4 58 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 77 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 77 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 285 (accept_3_4 55 77 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 285 (Polychromatic418967fa.accept_14_12_7_5_1_1107
  54 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 285 (accept_3_4 52 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 285 (accept_3_4 49 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 285 (accept_3_4 46 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 285 (Polychromatic418967fa.accept_18_9_5_15_1_2246 45 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 285 (accept_3_4 43 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 285 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 285
  (Polychromatic418967fa.accept_22_19_11_21_1_11454 41 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 77 285 (accept_3_4 40 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 77 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 77 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 285 (accept_3_4 37 77 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 285
  (Polychromatic418967fa.accept_21_15_14_12_1_8736 36 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 77 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 285 (accept_3_4 34 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 285 (accept_3_4 31 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 285 (accept_3_4 28 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 285 (accept_3_4 25 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 285 (Polychromatic418967fa.accept_18_6_5_15_1_7292 24 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 285 (accept_3_4 22 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 285 (accept_3_4 19 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 285 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 285 (accept_3_4 16 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 285 (accept_3_4 13 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 285 (accept_3_4 10 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 285 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 285 (accept_3_4 7 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  285 (Polychromatic418967fa.accept_18_6_5_15_1_7292 6 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 77 285 (Polychromatic418967fa.accept_17_5_9_13_1_1093 5 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 285 (accept_3_4 4 77 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 285 (accept_3_4 1 77 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 76 285
  (allA_succ_of_accept 75 76 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 76 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 285 (accept_3_5 74 76 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 285
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 285 (accept_3_5 71 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 69 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 285 (accept_3_5 68 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 66 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 285 (accept_3_5 65 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 285 (Polychromatic418967fa.accept_16_15_12_13_1_1045 63 76 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 285 (accept_3_5 62 76 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 285 (accept_3_5 59 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 285 (Polychromatic418967fa.accept_16_10_12_13_1_4950 58 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 76 285 19 3 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 76 285 (accept_3_5 56 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 76 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 285 (accept_3_5 53 76 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 52
  76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 285
  (Polychromatic418967fa.accept_10_1_6_5_1_304 51 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 285 (accept_3_5 50 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 285 (accept_3_5 47 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 76 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 285
  (Polychromatic418967fa.accept_18_9_4_15_1_555 45 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 285 (accept_3_5 44 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 285 (Polychromatic418967fa.accept_12_6_4_9_1_544 42 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 285 (accept_3_5 41 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 285 (Polychromatic418967fa.accept_13_1_11_12_1_1322 40 76 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 285 19 2 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 76 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 285 (accept_3_5 35 76 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 34
  76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 285
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 285 (accept_3_5 32 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 285 (accept_3_5 29 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 76 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 285
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 285 (accept_3_5 26 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 285 (accept_3_5 23 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 76 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 285 (accept_3_5 20 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 76
  285 19 1 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18
  76 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 76 285 (accept_3_5 17 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 76 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 76 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 76 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 285 (accept_3_5 14 76 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 285 (accept_3_5 11 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 285 (accept_3_5 8 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 285
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 285 (accept_3_5 5 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  285 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 76 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 76 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 285 (accept_3_5 2 76 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 285 (allA_succ_of_accept
  74 75 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 75 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 285 3 24 25 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 75 285 5 14 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 75 285 3 23 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 75 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 68 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 75 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 75 285 3 22 25 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 75 285 5 13 15 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 285
  (Polychromatic418967fa.accept_9_1_3_6_1_70 64 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 75 285 3 21 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 75 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 75 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 285 15 4 5 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 285
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 75 285 3 19 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 75 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 285 5 11 15 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 75 285 3 18 25 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 285 3 17 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 75 285 5 10 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 49
  75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 285 3 16 25 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 285 15 3 5 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 75 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 75 285 3 14 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 285 5 8 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 75 285 3 13 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 285
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 285 3 12 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 75 285 5 7 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 285 3 11 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 285 15 2 5 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 285 3 9 25 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 75 285 5 5 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 75 285 3 8 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 285 3 7 25 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 75 285 5 4 15 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 285
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 285 3 6 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 75 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 285 15 1 5 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 285 3 4 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 285 5 2 15 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 75 285 3 3 25 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 285 3 2 25 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 75 285 5 1 15 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 75 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 285 3 1 25 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 75 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 285 (allA_succ_of_accept
  73 74 285 (accept_3_4 73 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 285 (accept_3_4 70 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 68
  74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 285 (accept_3_4 67 74
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 285
  (Polychromatic418967fa.accept_9_3_2_6_1_264 66 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 285 (accept_3_4 64 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 62
  74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 285 (accept_3_4 61 74
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 285
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 285 (accept_3_4 58 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 285 (Polychromatic418967fa.accept_10_6_4_5_1_615
  56 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 285 (accept_3_4 55
  74 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 285
  (Polychromatic418967fa.accept_12_6_2_9_1_537 54 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 285 (accept_3_4 52 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 50
  74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 285 (accept_3_4 49 74
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 285 (accept_3_4 46 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 285 (Polychromatic418967fa.accept_17_11_6_13_1_10553 45 74 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 285 (accept_3_4 43 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 285 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 285 (accept_3_4 40 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 285
  (Polychromatic418967fa.accept_25_13_24_10_1_17432 38 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 74 285 (accept_3_4 37 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 74 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 285 (accept_3_4 34 74 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 285
  (Polychromatic418967fa.accept_22_11_8_21_1_17431 33 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 74 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 285 (accept_3_4 31 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 74 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 74 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 74 285 (accept_3_4 28 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  74 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 74 285 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 285 (accept_3_4 25 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 285 (Polychromatic418967fa.accept_17_7_6_13_1_10548 24 74 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 74 285 (accept_3_4 22 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  74 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 74 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 285 (accept_3_4 19 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 74 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 74 285 (accept_3_4 16 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  74 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 74 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 285 (accept_3_4 13 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 74 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 74 285 (accept_3_4 10 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  74 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 74 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 285 (accept_3_4 7 74 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 74 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 285 (accept_3_4 4 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 285 (accept_3_4 1 74 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  285 (allA_succ_of_accept 72 73 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 73 285 (accept_3_5 71 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 285 (Polychromatic418967fa.accept_11_3_7_10_1_180
  69 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 285 (accept_3_5 68
  73 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 285
  (Polychromatic418967fa.accept_9_4_1_6_1_284 67 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 73 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 66 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 285 (accept_3_5 65 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 285 (Polychromatic418967fa.accept_12_3_1_9_1_202
  63 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 285 (accept_3_5 62
  73 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 285
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 73 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 285 (accept_3_5 59 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 57
  73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 285 (accept_3_5 56 73
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 285
  (Polychromatic418967fa.accept_16_7_9_13_1_4948 55 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 73 285 (Polychromatic418967fa.accept_14_12_3_5_1_1868 54 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 285 (accept_3_5 53 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 51
  73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 285 (accept_3_5 50 73
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 285
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 73 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 285 (accept_3_5 47 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 285
  (Polychromatic418967fa.accept_21_3_10_12_1_10278 45 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 73 285 (accept_3_5 44 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 73 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 285 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 73 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 285 (accept_3_5 41 73 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 40
  73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 285 (accept_3_5 38 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 285 (accept_3_5 35 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 73 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 285
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 285 (accept_3_5 32 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 285 (accept_3_5 29 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 285
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 285 (accept_3_5 26 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 285 (Polychromatic418967fa.accept_21_3_10_12_1_10278 24 73 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 285 (accept_3_5 23 73 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 285 (accept_3_5 20 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 285 (Polychromatic418967fa.accept_20_19_13_5_1_7722 19 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 285 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 285 (accept_3_5 17 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 285 (accept_3_5 14 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 285 (accept_3_5 11 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 285 (accept_3_5 8 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  285 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 285 (Polychromatic418967fa.accept_16_6_9_13_1_2751 6 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 285 (accept_3_5 5 73 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 285 (accept_3_5 2 73 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 285 (allA_succ_of_accept 71
  72 285 (Polychromatic418967fa.accept_11_5_6_10_1_1432 71 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 285 (Polychromatic418967fa.accept_13_5_7_12_1_2757 70 72 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 285 3 23 24 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 285
  (Polychromatic418967fa.accept_10_8_2_5_1_596 68 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 285 3 22 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 285 (Polychromatic418967fa.accept_17_14_4_13_1_3018
  65 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 285
  (Polychromatic418967fa.accept_21_1_9_12_1_2719 64 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 285 3 21 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 285 (Polychromatic418967fa.accept_13_10_7_12_1_2782 62 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 285 (Polychromatic418967fa.accept_21_19_9_12_1_4071 61 72
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 285 3 20 24 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 285 3 19 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 285 (Polychromatic418967fa.accept_13_4_7_12_1_2823
  56 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 285
  (Polychromatic418967fa.accept_20_15_12_5_1_11958 55 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 72 285 3 18 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 72 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 72 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 52 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 72 285 3 17 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 72 285 (Polychromatic418967fa.accept_13_11_7_12_1_2758 50 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 285 (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 72
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 285 3 16 24 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 285
  (Polychromatic418967fa.accept_10_7_2_5_1_298 47 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 72 285 3 15 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 72 285 (Polychromatic418967fa.accept_13_5_7_12_1_2757
  44 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 285
  (Polychromatic418967fa.accept_10_3_2_5_1_295 43 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 285 3 14 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 285 (Polychromatic418967fa.accept_21_20_9_12_1_5549 41 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 285 (Polychromatic418967fa.accept_21_19_9_12_1_4071 40 72
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 285 3 13 24 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 72 285 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 285 3 12 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 285 (Polychromatic418967fa.accept_14_7_2_5_1_4528
  35 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 285
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 34 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 72 285 3 11 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 72 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 285 3 10 24 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 285
  (Polychromatic418967fa.accept_21_8_9_12_1_7118 29 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 72 285 3 9 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 72 285 (Polychromatic418967fa.accept_17_9_4_13_1_3057 26 72 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 285 3 8 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 285 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 285 (Polychromatic418967fa.accept_21_1_9_12_1_2719 22 72
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 285 3 7 24 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 285
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 72 285 (Polychromatic418967fa.accept_13_6_7_12_1_3504 19 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 285 3 6 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 285
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 72 285 3 5 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 72 285 (Polychromatic418967fa.accept_17_14_4_13_1_3018 14 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 285 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 72 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 285 3 4 24 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 72 285 3 3 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 72 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 72 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 285
  (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 285 3 2 24 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 285 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 72 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 285 3 1 24 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 285
  (Polychromatic418967fa.accept_21_2_9_12_1_4040 2 72 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 72 285 (Polychromatic418967fa.accept_21_1_9_12_1_2719 1 72 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 285 (allA_succ_of_accept 70
  71 285 (accept_3_4 70 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 285 (accept_3_4 67 71 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 65
  71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 285 (accept_3_4 64 71
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 285
  (Polychromatic418967fa.accept_12_3_11_9_1_193 63 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 71 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 285 (accept_3_4 61 71 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 71 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 59
  71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 285 (accept_3_4 58 71
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 285 (Polychromatic418967fa.accept_9_3_8_6_1_80
  57 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 285 (accept_3_4 55 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 285 (accept_3_4 52 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 285 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 71 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 285 (accept_3_4 49 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 285 (accept_3_4 46 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 71 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 285 (accept_3_4 43 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 285 (accept_3_4 40 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 71 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 285 (accept_3_4 37 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 285 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 285 (Polychromatic418967fa.accept_20_15_11_5_1_7737 35 71 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 285 (accept_3_4 34 71 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 285 (Polychromatic418967fa.accept_13_7_6_12_1_2027 33 71
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 285 (accept_3_4 31 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 285 (accept_3_4 28 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 71 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 285 (accept_3_4 25 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 285 (accept_3_4 22 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 71 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 285 (accept_3_4 19 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 285 (accept_3_4 16 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 285 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 71 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 285 (accept_3_4 13 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 285 (accept_3_4 10 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 71 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 285 (accept_3_4 7 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 71 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 285 (accept_3_4 4 71 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 285 (accept_3_4 1 71 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 285 (allA_succ_of_accept 69
  70 285 (Polychromatic418967fa.accept_13_4_5_12_1_751 69 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 70 285 (accept_3_5 68 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 70 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 66 70 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 70 285 5 13 14 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 70 285
  (Polychromatic418967fa.accept_9_1_7_6_1_75 64 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 70 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 285 (accept_3_5 62 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 70 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 70 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 285 5 12 14 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 285 (accept_3_5 59 70 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 70 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 285 (accept_3_5 56 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 70
  285 5 11 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  70 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 70 285 (accept_3_5 53 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 70 285 (Polychromatic418967fa.accept_16_4_6_13_1_1874 52 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 285 5 10 14 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 285
  (Polychromatic418967fa.accept_6_1_4_3_1_14 49 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 70 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 285 (accept_3_5 47 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 70 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 70 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 70 285 5 9 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 70 285 (accept_3_5 44 70 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 285
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 285 (accept_3_5 41 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  285 5 8 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 70 285 (accept_3_5 38 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 70 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 285 (Polychromatic418967fa.accept_16_4_6_13_1_1874 36 70
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 70 285 5 7 14 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 70 285
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 34 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 70 285 (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 285 (accept_3_5 32 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 70 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 285 5 6 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 285 (accept_3_5 29 70 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 70 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 285 (accept_3_5 26 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 70
  285 5 5 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  70 285 (Polychromatic418967fa.accept_17_7_2_13_1_5397 24 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 70 285 (accept_3_5 23 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 70 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 70 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 285 5 4 14 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 70 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 285 (accept_3_5 17 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 70 285 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 70 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 70 285 5 3 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 70 285 (accept_3_5 14 70 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 70 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 285 (accept_3_5 11 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  285 5 2 14 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 285 (Polychromatic418967fa.accept_16_9_6_13_1_3831 9 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 70 285 (accept_3_5 8 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 70 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 70 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 70 285 5 1 14 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 70 285
  (Polychromatic418967fa.accept_9_4_7_6_1_255 4 70 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 70 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 285 (accept_3_5 2 70 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 70 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 285 (allA_succ_of_accept 68 69
  285 (Polychromatic418967fa.accept_13_3_4_12_1_36 68 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 69 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 69 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 285 3 22 23 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 285
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 65 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 285 3 21 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  62 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 285
  (Polychromatic418967fa.accept_10_1_9_5_1_83 61 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 285 3 20 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 285 (Polychromatic418967fa.accept_13_7_4_12_1_1341 59 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 285 (Polychromatic418967fa.accept_16_10_5_13_1_8591 58 69
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 285 3 19 23 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 285
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 285 (Polychromatic418967fa.accept_13_3_4_12_1_36 55 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 285 3 18 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 53
  69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 285
  (Polychromatic418967fa.accept_21_10_6_12_1_5543 52 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 285 3 17 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 285 (Polychromatic418967fa.accept_16_1_5_13_1_1025 49 69
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 285 3 16 23 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 285
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 285 3 15 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 44
  69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 285 3 14 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 40 69
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 285 3 13 23 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 285
  (Polychromatic418967fa.accept_21_17_6_12_1_10174 38 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 69 285 (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 69 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 285 3 12 23 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 285
  (Polychromatic418967fa.accept_20_15_9_5_1_4684 35 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 34 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 285 3 11 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 32
  69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 285
  (Polychromatic418967fa.accept_10_1_9_5_1_83 31 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 69 285 3 10 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 69 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 285 (Polychromatic418967fa.accept_13_2_4_12_1_745 28 69 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 285 3 9 23 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 285
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 285 3 8 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 285 (Polychromatic418967fa.accept_21_2_6_12_1_5506 23 69 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 69 285 3 7 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 69 285 (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 285 (Polychromatic418967fa.accept_17_2_1_13_1_6670 19 69
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 285 3 6 23 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 285
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 285 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 285 3 5 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 69 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 285
  (Polychromatic418967fa.accept_25_13_19_10_1_3337 13 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 69 285 3 4 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 69 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 69 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 285
  (Polychromatic418967fa.accept_16_10_5_13_1_8591 10 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 285 3 3 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 69 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 285 3 2 23 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 285
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 285 3 1 23 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 285 (Polychromatic418967fa.accept_13_2_4_12_1_745 2 69 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 285
  (allA_succ_of_accept 67 68 285 (accept_3_4 67 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  68 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 285 (accept_3_4 64 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 285 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 285 (accept_3_4 61 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 285 (Polychromatic418967fa.accept_16_12_4_13_1_3827 60 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 285 (accept_3_4 58 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 285 (accept_3_4 55 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 285 (accept_3_4 52 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 285 (Polychromatic418967fa.accept_21_9_5_12_1_10145 51 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 285
  (Polychromatic418967fa.accept_20_10_8_5_1_7735 50 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 285 (accept_3_4 49 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 285 (accept_3_4 46 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 285 (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 285 (accept_3_4 43 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 285 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 285 (accept_3_4 40 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 285 (accept_3_4 37 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 285 (Polychromatic418967fa.accept_21_15_5_12_1_3987 36 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 285 (accept_3_4 34 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 285
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 285 (accept_3_4 31 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 285 (accept_3_4 28 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 285 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 285 (accept_3_4 25 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 285 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 285 (accept_3_4 22 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 285 (accept_3_4 19 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 285 (accept_3_4 16 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 285 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 285
  (Polychromatic418967fa.accept_20_14_8_5_1_6090 14 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 285 (accept_3_4 13 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 285 (accept_3_4 10 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 68 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 285 (accept_3_4 7 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  285 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 285 (accept_3_4 4 68 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 68 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  68 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 285 (accept_3_4 1 68 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 285 (allA_succ_of_accept 66 67
  285 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 285 (accept_3_5 65 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 285 (accept_3_5 62 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 285
  (Polychromatic418967fa.accept_17_9_16_13_1_6636 60 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 285 (accept_3_5 59 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 285 (accept_3_5 56 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 285 (accept_3_5 53 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 285 (accept_3_5 50 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 285 (Polychromatic418967fa.accept_13_10_2_12_1_1332 49 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 285 (accept_3_5 47 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 285 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 285 (accept_3_5 44 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 285 (accept_3_5 41 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 285 (accept_3_5 38 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 285 (accept_3_5 35 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 285 (accept_3_5 32 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 285 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 285 (accept_3_5 29 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 285 (accept_3_5 26 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 285
  (Polychromatic418967fa.accept_11_2_1_10_1_196 24 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 285 (accept_3_5 23 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 285 (accept_3_5 20 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 285 (accept_3_5 17 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 285 (accept_3_5 14 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 285 (accept_3_5 11 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 285 (accept_3_5 8 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 285 (accept_3_5 5 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 285 (accept_3_5 2 67 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 285 (allA_succ_of_accept 65 66
  285 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 285 3 21 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 62
  66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 285 3 20 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 285 3 19 22 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 285 3 18 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 285 3 17 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 285 3 16 22 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 285 3 15 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 44
  66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 285 3 14 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 285 3 13 22 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 285 3 12 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 285 3 11 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 285 3 10 22 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 285 3 9 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 285 3 8 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 285 3 7 22 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 285 3 6 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 285 3 5 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 285 3 4 22 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 285 3 3 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 285 3 2 22 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 66 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 285 3 1 22 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 66 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 285 (allA_succ_of_accept 64 65 285 (accept_3_4 64 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 65 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 285 (accept_3_4 61 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 65 285 5 12 13 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 65 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 285 (accept_3_4 58 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 65 285 5 11 13 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 65 285
  (Polychromatic418967fa.accept_25_4_15_10_1_17430 54 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 65 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 285 (accept_3_4 52 65 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 65 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 285 5 10 13 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 285 (accept_3_4 49 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 48
  65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 285
  (Polychromatic418967fa.accept_30_17_5_15_1_17429 47 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 65 285 (accept_3_4 46 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 65 285 5 9 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 65 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 285 (accept_3_4 43 65 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 65 285 (Polychromatic418967fa.accept_18_6_11_15_1_7255 42 65 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 285 5 8 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 65 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 285 (accept_3_4 37 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 36
  65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 285 5 7 13 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 285 (accept_3_4 34
  65 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 285
  (Polychromatic418967fa.accept_23_10_19_9_1_16042 33 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 285 (accept_3_4 31 65 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 65 285 5 6 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 65 285 (Polychromatic418967fa.accept_23_6_19_9_1_12717 29 65 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 285 (accept_3_4 28 65 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 285 5 5 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 285 (accept_3_4 22 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21
  65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 285 5 4 13 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 285 (accept_3_4 19
  65 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 285 (accept_3_4 16 65 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 285 5 3 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 285 (accept_3_4 13 65 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 65 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 285 5 2 13 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 285 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 65 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 285 (accept_3_4 7 65 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 285 (Polychromatic418967fa.accept_18_6_11_15_1_7255
  6 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 285 5 1 13 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 285 (accept_3_4 4 65
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 285 (Polychromatic418967fa.accept_7_3_2_5_1_147
  3 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 285 (accept_3_4 1 65 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 285 (allA_succ_of_accept 63 64 285
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 285 (accept_3_5 62 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 285 (accept_3_5 59 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 64 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 285 (accept_3_5 56 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 285 (Polychromatic418967fa.accept_12_6_4_9_1_544 54 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 285 (accept_3_5 53 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 64 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 285
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 285 (accept_3_5 50 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 285 (accept_3_5 47 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 64 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 285 (accept_3_5 44 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 285 (Polychromatic418967fa.accept_12_6_4_9_1_544 42 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 285 (accept_3_5 41 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 64 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 285 (accept_3_5 38 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 285 (accept_3_5 35 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 64 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 285
  (Polychromatic418967fa.accept_23_10_18_9_1_12811 33 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 64 285 (accept_3_5 32 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 64 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 285 (accept_3_5 29 64 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 285
  (Polychromatic418967fa.accept_21_7_1_12_1_13236 28 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 64 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 64 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 285 (accept_3_5 26 64 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 24
  64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 285 (accept_3_5 23 64
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 285
  (Polychromatic418967fa.accept_9_4_1_6_1_284 22 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 64 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 285 (accept_3_5 20 64 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 18
  64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 285 (accept_3_5 17 64
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 285
  (Polychromatic418967fa.accept_9_7_1_6_1_261 16 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 64 285 (Polychromatic418967fa.accept_20_15_4_5_1_7759 15 64 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 285 (accept_3_5 14 64 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 285 (accept_3_5 11 64
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 285 (Polychromatic418967fa.accept_7_3_1_5_1_44
  10 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 285
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 285 (accept_3_5 8 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 64 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 285 (accept_3_5 5 64 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 64 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 285 (accept_3_5 2 64 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 285 (allA_succ_of_accept 62 63 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 285 3 20 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  59 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 285 3 19 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 285 (Polychromatic418967fa.accept_13_4_11_12_1_1318 56 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 285 3 18 21 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 285
  (Polychromatic418967fa.accept_11_9_8_10_1_934 53 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 285 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 285 3 17 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 285
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 63 285 3 16 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 63 285 (Polychromatic418967fa.accept_10_7_3_5_1_301 47 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 285 3 15 21 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 285
  (Polychromatic418967fa.accept_14_2_7_5_1_5450 44 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 285 3 14 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 285
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 40 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 63 285 3 13 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 63 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 285 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 285 3 12 21 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 285
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 285 3 11 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 285 (Polychromatic418967fa.accept_10_2_3_5_1_996 32
  63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 285
  (Polychromatic418967fa.accept_11_9_8_10_1_934 31 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 285 3 10 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 285 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 285 3 9 21 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 285 3 8 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 285 3 7 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 285 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 285 3 6 21 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 285
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 285 (Polychromatic418967fa.accept_14_2_7_5_1_5450 16 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 285 3 5 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 285
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 285 3 4 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 285 3 3 21 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 285
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 285 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 285 3 2 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 285
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 63 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 285 3 1 21 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 285 (allA_succ_of_accept 61 62 285
  (accept_3_4 61 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 285 (accept_3_4 58 62 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 56
  62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 285 (accept_3_4 55 62
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 285
  (Polychromatic418967fa.accept_12_6_2_9_1_537 54 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 62 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 285 (accept_3_4 52 62 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 50
  62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 285 (accept_3_4 49 62
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 285 (Polychromatic418967fa.accept_9_3_8_6_1_80
  48 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 62 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 62 285 (accept_3_4 46 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  62 285 (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 62 285 (Polychromatic418967fa.accept_20_4_2_5_1_4607 44 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 285 (accept_3_4 43 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 62 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 62 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 62 285 (accept_3_4 40 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  62 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 62 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 285 (accept_3_4 37 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 62 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 285 (accept_3_4 34 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 285 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 285 (accept_3_4 31 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 62 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 285 (accept_3_4 28 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 285 (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 62 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 285 (accept_3_4 25 62 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 285 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 62
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 285 (accept_3_4 22 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 285 (accept_3_4 19 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 62 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 285 (accept_3_4 16 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 285 (accept_3_4 13 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 62 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 285 (accept_3_4 10 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 285 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 285 (accept_3_4 7 62 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 62 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 285 (accept_3_4 4 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 62 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 285 (accept_3_4 1 62 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 285
  (allA_succ_of_accept 60 61 285 (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 61 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 61 285 (accept_3_5 59 61 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 61 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 61 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 57
  61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 285 (accept_3_5 56 61
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 285 (Polychromatic418967fa.accept_9_1_7_6_1_75
  55 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 285
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 285 (accept_3_5 53 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 285 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 285 (accept_3_5 50 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 285 (accept_3_5 47 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 285 (Polychromatic418967fa.accept_22_1_17_21_1_8330 45 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 285 (accept_3_5 44 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 285 (Polychromatic418967fa.accept_17_9_10_13_1_6698 43 61
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 285
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 285 (accept_3_5 41 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 285 (accept_3_5 38 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 285
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 285 (accept_3_5 35 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 285 (Polychromatic418967fa.accept_25_8_11_10_1_17428 33 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 285 (accept_3_5 32 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 61 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 285 (accept_3_5 29 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 285 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 285 (accept_3_5 26 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 285 (Polychromatic418967fa.accept_21_4_19_12_1_10195 25 61
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 285
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 285 (accept_3_5 23 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 285 (accept_3_5 20 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 285
  (Polychromatic418967fa.accept_21_18_19_12_1_3982 18 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 61 285 (accept_3_5 17 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 61 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 285 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 61 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 285 (accept_3_5 14 61 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 13
  61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 285 (accept_3_5 11 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 285 (accept_3_5 8 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 285 (Polychromatic418967fa.accept_21_7_19_12_1_5579 7 61 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 285
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 285 (accept_3_5 5 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 285 (accept_3_5 2 61 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 61 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 285 (allA_succ_of_accept 59 60 285 (Polychromatic418967fa.accept_11_4_5_10_1_926 59 60 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 58 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 285 3 19 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 285 (Polychromatic418967fa.accept_13_4_8_12_1_3526 56 60 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 285 5 11 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 285 3 18 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 285 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  53 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 285
  (Polychromatic418967fa.accept_16_4_12_13_1_990 52 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 60 285 3 17 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 60 285 5 10 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 285 3 16 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 285
  (Polychromatic418967fa.accept_16_15_12_13_1_1045 47 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 60 285 (Polychromatic418967fa.accept_13_7_8_12_1_2810 46 60 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 285 15 3 4 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 285 3 14 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 285 5 8 12 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 285 3 13 20 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 60 285
  (Polychromatic418967fa.accept_17_4_9_13_1_2020 38 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 285 3 12 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 285 5 7 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 34
  60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 285 3 11 20 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 285
  (Polychromatic418967fa.accept_21_11_18_12_1_1494 32 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 60 285 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 60 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 285 15 2 4 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 285 (Polychromatic418967fa.accept_11_6_5_10_1_2724 28 60 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 285 3 9 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 285 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 60 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 285 5 5 12 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 285 3 8 20 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 60 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 285 3 7 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 285 5 4 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 285 (Polychromatic418967fa.accept_21_19_18_12_1_10350 19 60
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 285 3 6 20 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 285
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 60 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 285 15 1 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 285 (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 60 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 285 3 4 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 285 (Polychromatic418967fa.accept_18_11_6_15_1_5953 11 60 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 285 5 2 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 285 3 3 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 60 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 285
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 285 3 2 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 60 285 5 1 12 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 60 285 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 60 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 285 3 1 20 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 60 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 285 (allA_succ_of_accept 58
  59 285 (accept_3_4 58 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 285 (accept_3_4 55 59 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 53
  59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 285 (accept_3_4 52 59
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 285 (Polychromatic418967fa.accept_7_2_3_5_1_34
  51 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 285 (accept_3_4 49 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 285 (accept_3_4 46 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 285 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 59 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 285 (accept_3_4 43 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 41 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 285 (accept_3_4 40 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 59 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 285 (accept_3_4 37 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 285 (accept_3_4 34 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 285 (Polychromatic418967fa.accept_20_13_19_5_1_1012 33 59 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 285 (accept_3_4 31 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 285 (accept_3_4 28 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 285 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 59 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 285 (accept_3_4 25 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 285 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 285 (accept_3_4 22 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 285 (accept_3_4 19 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 285 (accept_3_4 16 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 285 (accept_3_4 13 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 285 (accept_3_4 10 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 59 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 285 (accept_3_4 7 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 285 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 59 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 285 (accept_3_4 4 59 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 285 (accept_3_4 1 59 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 285)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 285 (allA_succ_of_accept 57 58 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 285 (accept_3_5 56 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 285
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 58 285 (accept_3_5 53 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  58 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 285 (accept_3_5 50 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 58 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 285 (accept_3_5 47 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 285 (accept_3_5 44 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 285
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 285 (accept_3_5 41 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 40 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 285 (accept_3_5 38 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 285
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 285 (accept_3_5 35 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 285 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 285 (accept_3_5 32 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 285 (accept_3_5 29 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 285 (accept_3_5 26 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 285 (accept_3_5 23 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 285 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 285 (accept_3_5 20 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 285 (accept_3_5 17 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 285 (accept_3_5 14 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 285 (accept_3_5 11 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 285 (Polychromatic418967fa.accept_18_9_4_15_1_555 9 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 285 (accept_3_5 8 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 285
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 285 (accept_3_5 5 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  285 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 58 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 285 (accept_3_5 2 58 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 285 (allA_succ_of_accept 56 57 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 57 285 3 18 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 57 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 57 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 285 3 17 19 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 285
  (Polychromatic418967fa.accept_9_5_3_6_1_269 50 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 285 3 16 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 47
  57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 46 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 57 285 3 15 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 57 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 57 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 285 3 14 19 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 285 3 13 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 57 285 19 2 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 57 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 285 3 12 19 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 285 3 11 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 32
  57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 57 285 3 10 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 57 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 57 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 285 3 9 19 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 285 3 8 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 57 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 57 285 3 7 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 57 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 57 285 19 1 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 18 57 285 3 6 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 285 3 5 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 285 3 4 19 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 285 3 3 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 285 3 2 19 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 285 3 1 19 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 57 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 285))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 285 (allA_succ_of_accept 55 56 285 (accept_3_4 55 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 285 (accept_3_4 52 56 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 285 (Polychromatic418967fa.accept_10_1_6_5_1_304
  51 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 285 (accept_3_4 49 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 285 (accept_3_4 46 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 285 (Polychromatic418967fa.accept_21_3_14_12_1_8700 45 56 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 285 (accept_3_4 43 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 285 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 285 (accept_3_4 40 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 285
  (Polychromatic418967fa.accept_20_18_16_5_1_9137 38 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 285 (accept_3_4 37 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 285 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 285 (accept_3_4 34 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 285 (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 56 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 285 (accept_3_4 31 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 285 (accept_3_4 28 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 285 (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 56 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 285 (accept_3_4 25 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 285 (accept_3_4 22 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 285
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 285 (accept_3_4 19 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 285 (accept_3_4 16 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 285 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 56 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 285 (accept_3_4 13 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 285 (accept_3_4 10 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 56 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 285 (accept_3_4 7 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  285 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 285 (accept_3_4 4 56 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 285 (Polychromatic418967fa.accept_11_2_1_10_1_196 2
  56 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 285 (accept_3_4 1 56 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 285))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 285 (allA_succ_of_accept 54 55 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 285 (accept_3_5 53 55 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 285
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 55 285 5 10 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 55 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 285 (accept_3_5 47 55 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 285 5 9 11 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 285 (accept_3_5 44
  55 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 285 (accept_3_5 41 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 55 285 5 8 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 55 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 55 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 285 (accept_3_5 38 55 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 285 (Polychromatic418967fa.accept_17_3_4_13_1_2030 37 55 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 55 285 5 7 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 55 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 285 (Polychromatic418967fa.accept_20_13_15_5_1_4628 33 55
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 285 (accept_3_5 32 55 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 31
  55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 285 5 6 11 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 285 (accept_3_5 29
  55 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 285
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 55 285 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 285 (accept_3_5 26 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 55 285 5 5 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 55 285 (Polychromatic418967fa.accept_20_4_15_5_1_10633 24 55 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 285 (accept_3_5 23 55 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 55 285 5 4 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 55 285 (Polychromatic418967fa.accept_20_19_15_5_1_11974 19 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 285 (accept_3_5 17 55 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 285 5 3 11 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 285 (accept_3_5 14
  55 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 285
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 55 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 285 (accept_3_5 11 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 55 285 5 2 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 55 285 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 55 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 285 (accept_3_5 8 55 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 55 285 5 1 11 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 55 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 285 (accept_3_5 2 55 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 285 (allA_succ_of_accept 53 54 285
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 53 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 285 3 17 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 50
  54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 285
  (Polychromatic418967fa.accept_10_9_4_5_1_616 49 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 285 3 16 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 54 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 285 3 15 18 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 285
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 285 3 14 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 285 (Polychromatic418967fa.accept_10_1_4_5_1_1031
  41 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 285
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 54 285 3 13 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 54 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 285 (Polychromatic418967fa.accept_23_14_8_9_1_4397 37 54
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 285 3 12 18 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 285 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 285 3 11 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 285 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  32 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 285 3 10 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 285 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 54 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 285 3 9 18 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 285
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 285 (Polychromatic418967fa.accept_16_9_6_13_1_3831 25 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 285 3 8 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 285
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 285 3 7 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 285 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 285 3 6 18 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 285
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 285 3 5 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 54 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 285
  (Polychromatic418967fa.accept_22_13_10_21_1_17427 13 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 54 285 3 4 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 54 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 285 (Polychromatic418967fa.accept_12_10_6_9_1_549
  10 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 285 3 3 18 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 285
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 285 3 2 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 285 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 54 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 285
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 54 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 285 3 1 18 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 54 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 285 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 54 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  285)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 285 (allA_succ_of_accept 52 53 285 (accept_3_4
  52 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 285 (accept_3_4 49 53 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 47
  53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 285 (accept_3_4 46 53
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 285
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 285 (accept_3_4 43 53 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 285 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 285 (accept_3_4 40 53
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 285 (Polychromatic418967fa.accept_9_3_8_6_1_80
  39 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 285 (accept_3_4 37 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 285 (Polychromatic418967fa.accept_17_1_2_13_1_2026 35 53 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 285 (accept_3_4 34 53 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 285 (Polychromatic418967fa.accept_16_1_5_13_1_1025 33 53
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 285 (accept_3_4 31 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 285 (accept_3_4 28 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 53 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 285 (accept_3_4 25 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 285 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 285 (accept_3_4 22 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 285 (accept_3_4 19 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 285 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 285 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 285 (accept_3_4 16 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 53 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 285 (accept_3_4 13 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 285 (accept_3_4 10 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 53 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 285 (accept_3_4 7 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  285 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 285 (accept_3_4 4 53 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 53 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 285 (accept_3_4 1 53 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 285)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 285 (allA_succ_of_accept 51 52 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 285 (accept_3_5 50 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 285 (accept_3_5 47 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 285 (Polychromatic418967fa.accept_18_9_16_15_1_2241 45 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 285 (accept_3_5 44 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 285
  (Polychromatic418967fa.accept_11_9_8_10_1_934 42 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 285 (accept_3_5 41 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 285 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 285 (accept_3_5 38 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 285 (accept_3_5 35 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 285 (Polychromatic418967fa.accept_22_12_8_21_1_14501 34 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 285 (accept_3_5 32 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 285 (accept_3_5 29 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 285 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 285 (accept_3_5 26 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 285
  (Polychromatic418967fa.accept_16_8_4_13_1_1014 24 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 285 (accept_3_5 23 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 285 (accept_3_5 20 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 285
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 285 (accept_3_5 17 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 285 (accept_3_5 14 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 285 (accept_3_5 11 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 285 (accept_3_5 8 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 285
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 285 (accept_3_5 5 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  285 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 52 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 285 (accept_3_5 2 52 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 285))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 285 (allA_succ_of_accept 50 51 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 285
  (Polychromatic418967fa.accept_10_9_1_5_1_594 49 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 51 285 3 16 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 51 285 (Polychromatic418967fa.accept_11_3_7_10_1_180 47 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 285 3 15 17 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 285
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 285 3 14 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 285
  (Polychromatic418967fa.accept_16_8_3_13_1_7295 40 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 51 285 3 13 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 51 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 51 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 285 3 12 17 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 285
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 285 3 11 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 32
  51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 285 3 10 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 285 (Polychromatic418967fa.accept_22_6_7_21_1_17426 28 51
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 285 3 9 17 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 285 3 8 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 285 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 51 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 285 3 7 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 285 (Polychromatic418967fa.accept_21_20_9_12_1_5549 20 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 51 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 285 3 6 17 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 285 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 285 3 5 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 285
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 285 3 4 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 285 3 3 17 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 285
  (Polychromatic418967fa.accept_16_8_3_13_1_7295 8 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 285 3 2 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 51 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 285 3 1 17 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 51 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  285))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 285 (allA_succ_of_accept 49 50 285 (accept_3_4 49
  50 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 285 (accept_3_4 46 50 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 50 285 5 9 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 50 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 50 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 285 (accept_3_4 43 50 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 50 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 50 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 285 5 8 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 50 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 285 (accept_3_4 37 50 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 285
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 50 285 5 7 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 50 285 (accept_3_4 34 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 50 285 (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 50 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 50 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 285 (accept_3_4 31 50 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 285 5 6 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29
  50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 285 (accept_3_4 28 50
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 285 (Polychromatic418967fa.accept_4_3_2_1_1_50
  27 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 285 5 5 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 50 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 285 (accept_3_4 22 50 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21
  50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 285 5 4 10 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 285 (accept_3_4 19
  50 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 285 (accept_3_4 16 50 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 50 285 5 3 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 50 285 (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 50 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 285 (accept_3_4 13 50 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 50 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 285 5 2 10 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 285 (Polychromatic418967fa.accept_17_9_16_13_1_6636 9 50 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 50 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 285 (accept_3_4 7 50 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6
  50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 285 5 1 10 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 285 (accept_3_4 4 50
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 285 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 285
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 50 285 (accept_3_4 1 50 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  285)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 285 (allA_succ_of_accept 48 49 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 285 (accept_3_5 47 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 285 (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 49 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 285 (accept_3_5 44 49 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 49 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 285
  (Polychromatic418967fa.accept_17_8_15_13_1_7942 42 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 285 (accept_3_5 41 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 285 (accept_3_5 38 49 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 285
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 285 (accept_3_5 35 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 285 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 49 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 285 (accept_3_5 32 49 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 285 (accept_3_5 29 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 285 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 285 (accept_3_5 26 49 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 285
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 285 (accept_3_5 23 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 285 (accept_3_5 20 49 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 285
  (Polychromatic418967fa.accept_21_18_7_12_1_10175 18 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 49 285 (accept_3_5 17 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 49 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 285 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 49 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 285 (accept_3_5 14 49 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 285
  (Polychromatic418967fa.accept_23_13_3_9_1_17425 13 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 49 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 285 (accept_3_5 11 49 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 49 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 285 (Polychromatic418967fa.accept_13_9_10_12_1_2048
  9 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 285 (accept_3_5 8 49
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 285 (Polychromatic418967fa.accept_9_7_4_6_1_273
  7 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 285
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 285 (accept_3_5 5 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 49 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 285 (accept_3_5 2 49 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 285))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 285 (allA_succ_of_accept 47 48 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 46
  48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 285 3 15 16 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 285 3 14 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 285 3 13 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 48 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 285 3 12 16 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 285 3 11 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 32
  48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 285 3 10 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 48 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 285 3 9 16 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 285 3 8 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 48 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 22 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 285 3 7 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 48 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 285 3 6 16 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 285 3 5 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 48 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 285 3 4 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 48 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 285 3 3 16 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 285 3 2 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 48 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 285 3 1 16 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 48 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  285)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 285 (allA_succ_of_accept 46 47 285 (accept_3_4 46 47
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 285
  (Polychromatic418967fa.accept_18_9_11_15_1_4616 45 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 285 (accept_3_4 43 47 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 41
  47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 285 (accept_3_4 40 47
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 285
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 285 (accept_3_4 37 47 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 285 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 47 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 285 (accept_3_4 34 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 285 (accept_3_4 31 47 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 285
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 285 (accept_3_4 28 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 285 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 285 (accept_3_4 25 47 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 285 (Polychromatic418967fa.accept_18_6_11_15_1_7255 24 47 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 285 (accept_3_4 22 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 285 (accept_3_4 19 47 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 285 (accept_3_4 16 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 285 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 285 (accept_3_4 13 47 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 285
  (Polychromatic418967fa.accept_21_11_5_12_1_10218 11 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 47 285 (accept_3_4 10 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 47 285 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 47 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 285 (accept_3_4 7 47 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 285 (accept_3_4 4 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  285 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 285 (accept_3_4 1 47 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 285))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 285 (allA_succ_of_accept 45
  46 285 (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 46 285 (accept_3_5 44 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 46 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 46 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 285 (accept_3_5 41 46 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 40
  46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 285 (accept_3_5 38 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 285 (accept_3_5 35 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 46 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 285
  (Polychromatic418967fa.accept_16_1_14_13_1_3834 33 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 285 (accept_3_5 32 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 285 (accept_3_5 29 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 285 (Polychromatic418967fa.accept_17_11_12_13_1_3030 28 46 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 285 (accept_3_5 26 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 285 (accept_3_5 23 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 46 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 285 (accept_3_5 20 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 285 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 285 (accept_3_5 17 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 46 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 285 (accept_3_5 14 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 285 (accept_3_5 11 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 285 (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 46 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 285 (accept_3_5 8 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 46 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 285 (accept_3_5 5 46 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 46 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 285 (accept_3_5 2 46 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  285)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 285 (allA_succ_of_accept 44 45 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 45 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 285 3 14 15 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 285 (Polychromatic418967fa.accept_13_2_6_12_1_1334
  41 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 285 5 8 9 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 45 285 3 13 15 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 285
  (Polychromatic418967fa.accept_21_17_3_12_1_3986 38 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 45 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 285 3 12 15 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 45 285 5 7 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 285 (Polychromatic418967fa.accept_18_16_9_15_1_4614
  34 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 285 3 11 15 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 285
  (Polychromatic418967fa.accept_17_15_11_13_1_2039 32 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 45 285 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 45 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 285 15 2 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 29
  45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 285
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 28 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 285 3 9 15 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 285 (Polychromatic418967fa.accept_14_12_3_5_1_1868 26 45 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 285 5 5 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 285 3 8 15 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 45 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 22 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 285 3 7 15 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 45 285 5 4 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 285 (Polychromatic418967fa.accept_23_19_22_9_1_16008 19 45 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 285 3 6 15 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 285 (Polychromatic418967fa.accept_18_17_9_15_1_7268 17 45
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 285 15 1 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 285 (Polychromatic418967fa.accept_21_14_3_12_1_10169 14 45 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 285 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 45 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 285 3 4 15 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 285
  (Polychromatic418967fa.accept_18_11_9_15_1_5988 11 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 45 285 5 2 9 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 45 285 3 3 15 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 45 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 285 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 45 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 285 3 2 15 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 45 285 5 1 9 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 285
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 45 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 285 3 1 15 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 45 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  285))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 285 (allA_succ_of_accept 43 44 285 (accept_3_4 43 44
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 285
  (Polychromatic418967fa.accept_12_6_8_9_1_553 42 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 285 (accept_3_4 40 44 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 38
  44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 285 (accept_3_4 37 44
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 285
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 285 (accept_3_4 34 44 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 32
  44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 285 (accept_3_4 31 44
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 285 (Polychromatic418967fa.accept_9_3_8_6_1_80
  30 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 285 (accept_3_4 28 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 285 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 285 (accept_3_4 25 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 44 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 285 (accept_3_4 22 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 285 (accept_3_4 19 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 44 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 285 (accept_3_4 16 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 285 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 285 (accept_3_4 13 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 44 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 285 (accept_3_4 10 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 285 (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 285 (accept_3_4 7 44 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 44 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 285 (accept_3_4 4 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  285 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 44 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 44 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 285 (accept_3_4 1 44 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 285)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 285 (allA_succ_of_accept 42 43
  285 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 285 (accept_3_5 41 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 285 (accept_3_5 38 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 43 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 285
  (Polychromatic418967fa.accept_21_15_1_12_1_10209 36 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 43 285 (accept_3_5 35 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 43 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 285 (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 43
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 285 (accept_3_5 32 43 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 31
  43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 285 (accept_3_5 29 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 285 (accept_3_5 26 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 285 (accept_3_5 23 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 285 (accept_3_5 20 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 43 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 285 (accept_3_5 17 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 285 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 285 (accept_3_5 14 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 285 (accept_3_5 11 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 285 (Polychromatic418967fa.accept_21_9_1_12_1_3984 9 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 285 (accept_3_5 8 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 285 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 285 (accept_3_5 5 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 285 (accept_3_5 2 43 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 285))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 285
  (allA_succ_of_accept 41 42 285 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 42 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 42 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 285 3 13 14 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 285
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 285 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 42 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 285 3 12 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 285
  (Polychromatic418967fa.accept_11_1_9_10_1_184 34 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 285 3 11 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 285 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 42 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 285 3 10 14 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 285
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 29 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 42 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 285 3 9 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 42 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 285
  (Polychromatic418967fa.accept_28_25_14_5_1_17424 25 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 42 285 3 8 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 285 (Polychromatic418967fa.accept_12_10_6_9_1_549
  22 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 285 3 7 14 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 285
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 285 3 6 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 285 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 42 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 285
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 285 3 5 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 42 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 285 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 42 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 285 3 4 14 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 285 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 42 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 285 3 3 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 42 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 285 3 2 14 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 285 (Polychromatic418967fa.accept_16_5_10_13_1_6042 5 42 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 42 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 285 3 1 14 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 285
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 42 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 285 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 42 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 285)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 285
  (allA_succ_of_accept 40 41 285 (accept_3_4 40 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 285 (accept_3_4 37 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 285 (accept_3_4 34 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 285 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 285 (accept_3_4 31 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 41 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 285 (accept_3_4 28 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 285 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 285 (accept_3_4 25 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 285 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 41 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 285
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 285 (accept_3_4 22 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 285 (accept_3_4 19 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 41 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 285
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 285 (accept_3_4 16 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 285 (accept_3_4 13 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 285 (accept_3_4 10 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 285 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 285 (accept_3_4 7 41 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 285 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 41 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 285
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 285 (accept_3_4 4 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  285 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 41 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 285 (accept_3_4 1 41 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 285))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 285 (allA_succ_of_accept 39 40 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 285 (accept_3_5 38 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 285 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 40 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 285 5 7 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 34
  40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 285
  (Polychromatic418967fa.accept_22_11_18_21_1_12992 33 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 40 285 (accept_3_5 32 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 40 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 285 5 6 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 285 (accept_3_5 29 40 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 40 285 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 40 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 285
  (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 285 (accept_3_5 26 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40
  285 5 5 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  40 285 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 40 285 (accept_3_5 23 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 40 285 (Polychromatic418967fa.accept_21_1_19_12_1_5562 22 40 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 285 5 4 8 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 285
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 40 285 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 40 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 285 (accept_3_5 17 40 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 40 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 40 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 40 285 5 3 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 40 285 (accept_3_5 14 40 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 285 (accept_3_5 11 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  285 5 2 8 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40
  285 (Polychromatic418967fa.accept_18_9_4_15_1_555 9 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 40 285 (accept_3_5 8 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 40 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 40 285 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 40 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 40 285 5 1 8 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 40 285
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 4 40 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 40 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 40 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 285 (accept_3_5 2 40 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 40 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 285)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 285
  (allA_succ_of_accept 38 39 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 39 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 285 3 12 13 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 39 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 39 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 39 285 3 11 13 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 39 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  39 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 39 285 3 10 13 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 39 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 39 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 285 3 9 13 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 285 3 8 13 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 39 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 39 285 3 7 13 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 39 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 39 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 285 3 6 13 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 39 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 285 3 5 13 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 39 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 39 285 3 4 13 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 285 3 3 13 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 39 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 285 3 2 13 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 39 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 285 3 1 13 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 39 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 285)))))))))))))))))))))))))))))))))))))))
  (allB_succ 38 285 (allA_succ_of_accept 37 38 285 (accept_3_4 37 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 38 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 38 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 38 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 285 (accept_3_4 34 38 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 285 (Polychromatic418967fa.accept_10_3_8_5_1_606
  33 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 285 (accept_3_4 31 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 285 (accept_3_4 28 38 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 285
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 285 (accept_3_4 25 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 285 (Polychromatic418967fa.accept_21_3_17_12_1_5530 24 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 285 (accept_3_4 22 38 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 285
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 20 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 19 38 285 19 1 2 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 18 38 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 38 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 38 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 285 (accept_3_4 16 38 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 285
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 285 (accept_3_4 13 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 285 (accept_3_4 10 38 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 38 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 285 (accept_3_4 7 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  285 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 38 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 285 (accept_3_4 4 38 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 38 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 38 285 (accept_3_4 1 38 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  285)))))))))))))))))))))))))))))))))))))) (allB_succ 37 285 (allA_succ_of_accept 36 37 285
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 37 285 (accept_3_5 35 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 37 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 37 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 285 (accept_3_5 32 37 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 31
  37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 285 (accept_3_5 29 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 285 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 37 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 285 (accept_3_5 26 37 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 285
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 285 (accept_3_5 23 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 37 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 285 (accept_3_5 20 37 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 285 (Polychromatic418967fa.accept_25_19_12_10_1_12447 19 37 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 285
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 285 (accept_3_5 17 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 285 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 37 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 285 (accept_3_5 14 37 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 37 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 285 (accept_3_5 11 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 285 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 37 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 285 (accept_3_5 8 37 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 37 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 285
  (Polychromatic418967fa.accept_21_6_16_12_1_1490 6 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 285 (accept_3_5 5 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 37 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 285 (accept_3_5 2 37 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 285 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 37 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 285))))))))))))))))))))))))))))))))))))) (allB_succ 36 285
  (allA_succ_of_accept 35 36 285 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 36 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 36 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 285 3 11 12 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 285
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 36 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 285 3 10 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  29 36 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 285
  (Polychromatic418967fa.accept_13_2_10_12_1_757 28 36 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 285 3 9 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 285 (Polychromatic418967fa.accept_21_5_15_12_1_5519 26 36 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 285 3 8 12 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 285
  (Polychromatic418967fa.accept_16_7_4_13_1_1057 23 36 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 285 (Polychromatic418967fa.accept_13_9_10_12_1_2048 22 36 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 285 3 7 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 36 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 285
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 36 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 285 3 6 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 285 (Polychromatic418967fa.accept_23_16_13_9_1_16005 16 36
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 285 3 5 12 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 285
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 285 3 4 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 36 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 285 3 3 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 285 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 36 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 36 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 285 3 2 12 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 285
  (Polychromatic418967fa.accept_21_5_15_12_1_5519 5 36 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 36 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 285 3 1 12 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 285 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 36 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 285
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 285)))))))))))))))))))))))))))))))))))) (allB_succ 35 285 (allA_succ_of_accept 34 35 285 (accept_3_4 34
  35 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 285
  (Polychromatic418967fa.accept_16_1_3_13_1_2785 33 35 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 285 (accept_3_4 31 35 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 285 5 6 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 35 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 285 (accept_3_4 28 35 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 285 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 35 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 285 5 5 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 285 (Polychromatic418967fa.accept_16_8_3_13_1_7295 24 35 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 285 (accept_3_4 22 35 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  35 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 285 5 4 7 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 285 (accept_3_4 19
  35 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 285 (Polychromatic418967fa.accept_16_1_3_13_1_2785 17 35 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 285 (accept_3_4 16 35 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 285 5 3 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 285 (accept_3_4 13 35 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 285 5 2 7 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 285 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 35 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 285 (accept_3_4 7 35 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 285 5 1 7 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 285 (accept_3_4 4 35
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 285 (Polychromatic418967fa.accept_9_3_8_6_1_80
  3 35 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 285 (accept_3_4 1 35 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  285))))))))))))))))))))))))))))))))))) (allB_succ 34 285 (allA_succ_of_accept 33 34 285
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 285 (accept_3_5 32 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 34 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 285 (accept_3_5 29 34 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 34 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 285 (accept_3_5 26 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 285 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 34 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 285 (accept_3_5 23 34 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 34 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 285 (accept_3_5 20 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 34 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 285 (accept_3_5 17 34 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 34 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 285 (accept_3_5 14 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 34 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 285 (accept_3_5 11 34 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 34 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 285
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 285 (accept_3_5 8 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 34 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 285 (accept_3_5 5 34 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 34 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 285 (accept_3_5 2 34 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 285))))))))))))))))))))))))))))))))))
  (allB_succ 33 285 (allA_succ_of_accept 32 33 285 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 33 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 285
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 33 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 285 3 10 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 285 (Polychromatic418967fa.accept_17_12_16_13_1_7951 29 33 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 33 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 285 3 9 11 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 285
  (Polychromatic418967fa.accept_17_9_16_13_1_6636 26 33 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 285 (Polychromatic418967fa.accept_16_9_1_13_1_1850 25 33 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 285 3 8 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 285 (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 33
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 285
  (Polychromatic418967fa.accept_10_2_3_5_1_996 22 33 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 285 3 7 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 33 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 285 (Polychromatic418967fa.accept_13_6_7_12_1_3504 19 33
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 285 3 6 11 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 285
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 33 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 285 (Polychromatic418967fa.accept_25_16_8_10_1_12376 16 33 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 285 3 5 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 285 (Polychromatic418967fa.accept_16_14_1_13_1_2754 14 33
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 285
  (Polychromatic418967fa.accept_23_13_10_9_1_17423 13 33 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 33 285 3 4 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 33 285 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 33 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 285
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 33 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 285 3 3 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 285 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 33 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 285 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 33 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 285 3 2 11 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 285
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 33 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 33 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 285 3 1 11 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 285 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 33 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 285
  (Polychromatic418967fa.accept_22_1_11_21_1_6612 1 33 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 285))))))))))))))))))))))))))))))))) (allB_succ 32 285 (allA_succ_of_accept 31 32 285 (accept_3_4 31 32
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 285 (accept_3_4 28 32 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 32 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 26
  32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 285 (accept_3_4 25 32
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 285
  (Polychromatic418967fa.accept_21_3_11_12_1_10183 24 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 285 (accept_3_4 22 32 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 285
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 285 (accept_3_4 19 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 285 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 285 (accept_3_4 16 32 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 32 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 285
  (Polychromatic418967fa.accept_21_14_11_12_1_10182 14 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 32 285 (accept_3_4 13 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 32 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 32 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 285 (accept_3_4 10 32 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9
  32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 285 (accept_3_4 7 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  285 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 285 (accept_3_4 4 32 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  32 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 285 (accept_3_4 1 32 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 285)))))))))))))))))))))))))))))))) (allB_succ 31 285
  (allA_succ_of_accept 30 31 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 285 (accept_3_5 29 31 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 285 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  27 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 285 (accept_3_5 26
  31 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 285
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 285 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 31 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 285 (accept_3_5 23 31 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 285 (accept_3_5 20 31
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 285 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 285 (accept_3_5 17 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 31 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 285 (accept_3_5 14 31 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 285 (Polychromatic418967fa.accept_22_13_9_21_1_9862 13 31 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 285 (accept_3_5 11 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 31 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 285 (accept_3_5 8 31 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 285 (accept_3_5 5 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 285 (accept_3_5 2 31 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 285))))))))))))))))))))))))))))))) (allB_succ 30 285
  (allA_succ_of_accept 29 30 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 30 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 30 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 285 3 9 10 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 30 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 30 285 5 5 6 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 30 285 3 8 10 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 30 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 285 3 7 10 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 285 5 4 6 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 285
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 285 3 6 10 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 30 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 30 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 285 15 1 2 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 285
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 30 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 30 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 285 3 4 10 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 285 5 2 6 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 285 3 3 10 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 30 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 285 3 2 10 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 285 5 1 6 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 30 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 285 3 1 10 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 30 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 30 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 285)))))))))))))))))))))))))))))) (allB_succ 29 285 (allA_succ_of_accept
  28 29 285 (accept_3_4 28 29 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 285
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 29 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 285 (accept_3_4 25 29 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 23
  29 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 285 (accept_3_4 22 29
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 285
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 285 (accept_3_4 19 29 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 29 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 17
  29 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 285 (accept_3_4 16 29
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 285
  (Polychromatic418967fa.accept_12_3_5_9_1_176 15 29 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 285 (accept_3_4 13 29 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 29 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 11
  29 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 285 (accept_3_4 10 29
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 285
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 29 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 285 (accept_3_4 7 29 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  29 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 285 (accept_3_4 4 29 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 285 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 29
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 285 (accept_3_4 1 29 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  285))))))))))))))))))))))))))))) (allB_succ 28 285 (allA_succ_of_accept 27 28 285
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 285 (accept_3_5 26 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 285 (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 28 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 285 (accept_3_5 23 28 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 28 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 285 (accept_3_5 20 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 285 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 285 (accept_3_5 17 28 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 285 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 28 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 285
  (Polychromatic418967fa.accept_16_15_12_13_1_1045 15 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 28 285 (accept_3_5 14 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 28 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 28 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 285 (accept_3_5 11 28 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 285
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 28 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 28 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 285 (accept_3_5 8 28 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 28 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 285 (Polychromatic418967fa.accept_12_6_4_9_1_544 6
  28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 285 (accept_3_5 5 28 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 4
  28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 285
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 285 (accept_3_5 2 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 285)))))))))))))))))))))))))))) (allB_succ 27 285 (allA_succ_of_accept 26 27 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 27 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 285 3 8 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 285 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 27 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 285 3 7 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 285 (Polychromatic418967fa.accept_14_6_13_5_1_534 20 27 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 27 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 285 3 6 9 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 285
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 27 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 285 (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 27 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 285 3 5 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 285
  (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 285 3 4 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 285 3 3 9 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 27 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 285 3 2 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 285 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 27 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 285
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 285 3 1 9 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 27 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 285))))))))))))))))))))))))))) (allB_succ 26
  285 (allA_succ_of_accept 25 26 285 (accept_3_4 25 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 26 285 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 285 (accept_3_4 22 26 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 285
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 285 (accept_3_4 19 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 285 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 285 (accept_3_4 16 26 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 285
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 285 (accept_3_4 13 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 285 (accept_3_4 10 26 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 26 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 285
  (Polychromatic418967fa.accept_21_8_5_12_1_10219 8 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 285 (accept_3_4 7 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  285 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 26 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 285 (accept_3_4 4 26 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 26
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 285 (accept_3_4 1 26 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 285)))))))))))))))))))))))))) (allB_succ 25 285
  (allA_succ_of_accept 24 25 285 (Polychromatic418967fa.accept_21_3_4_12_1_1462 24 25 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 285 (accept_3_5 23 25 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  25 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 285 5 4 5 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 285
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 25 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 25 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 285 (accept_3_5 17 25 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 25 285 5 3 5 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 25 285 (accept_3_5 14 25 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 285
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 25 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 285 (accept_3_5 11 25 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25
  285 5 2 5 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25
  285 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 285 (accept_3_5 8 25 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  285 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 25 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 25 285 5 1 5 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 25 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 25 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 285 (accept_3_5 2 25 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  285 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 285))))))))))))))))))))))))) (allB_succ 24 285 (allA_succ_of_accept 23 24 285
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 24 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 285 3 7 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 285 (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 24
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 285
  (Polychromatic418967fa.accept_10_9_4_5_1_616 19 24 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 285 3 6 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 285 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 24 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 24 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 24 285 3 5 8 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 24 285
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 24 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 285 (Polychromatic418967fa.accept_21_13_3_12_1_10213 13 24 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 285 3 4 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 285 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 24 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 285
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 24 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 24 285 3 3 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 24 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 24 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 285 (Polychromatic418967fa.accept_13_7_11_12_1_2051
  7 24 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 285 3 2 8 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 285
  (Polychromatic418967fa.accept_16_5_8_13_1_2764 5 24 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 285 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 24 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 285 3 1 8 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 24 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 285)))))))))))))))))))))))) (allB_succ 23 285 (allA_succ_of_accept 22 23 285 (accept_3_4 22 23 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 21
  23 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 285 (accept_3_4 19 23 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 23 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 285 (accept_3_4 16 23 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 285 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 23 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 285 (accept_3_4 13 23 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 23 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 285 (accept_3_4 10 23 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 285 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 23 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 285 (accept_3_4 7 23 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 285 (Polychromatic418967fa.accept_22_5_1_21_1_8294 5 23 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 285 (accept_3_4 4 23 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 23 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 285 (accept_3_4 1 23 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 285))))))))))))))))))))))) (allB_succ 22 285
  (allA_succ_of_accept 21 22 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 285 (accept_3_5 20 22 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 22 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 18
  22 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 285 (accept_3_5 17 22
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 285
  (Polychromatic418967fa.accept_9_7_4_6_1_273 16 22 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 22 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 285 (accept_3_5 14 22 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 22 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 12
  22 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 285 (accept_3_5 11 22
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 285 (Polychromatic418967fa.accept_7_3_1_5_1_44
  10 22 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 285
  (Polychromatic418967fa.accept_16_9_6_13_1_3831 9 22 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 285 (accept_3_5 8 22 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 22 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 285 (accept_3_5 5 22 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 22 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 285 (accept_3_5 2 22 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 285)))))))))))))))))))))) (allB_succ 21
  285 (allA_succ_of_accept 20 21 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 285 3 6 7 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 285 3 5 7 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 285 3 4 7 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 285 3 3 7 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 285
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 285 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 21 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 285 3 2 7 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 285
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 285 3 1 7 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 285 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 285))))))))))))))))))))) (allB_succ 20 285
  (allA_succ_of_accept 19 20 285 (accept_3_4 19 20 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 20 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 285 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 285 (accept_3_4 16 20 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 20 285 5 3 4 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 20 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 20 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 285 (accept_3_4 13 20 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 20 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 285 5 2 4 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 20 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 20 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 285 (accept_3_4 7 20 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 285 (Polychromatic418967fa.accept_12_6_8_9_1_553 6
  20 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 285 5 1 4 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 285 (accept_3_4 4 20
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 285 (Polychromatic418967fa.accept_9_3_2_6_1_264
  3 20 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 285
  (Polychromatic418967fa.accept_30_2_20_15_1_17422 2 20 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 285 (accept_3_4 1 20 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  285)))))))))))))))))))) (allB_succ 19 285 (allA_succ_of_accept 18 19 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  19 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 285 (accept_3_5 17 19
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 285 (Polychromatic418967fa.accept_6_4_1_3_1_77
  16 19 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 285
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 19 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 285 (accept_3_5 14 19 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  19 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 19 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 19 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 285 (accept_3_5 11 19 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 285
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 19 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 285 (accept_3_5 8 19 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  285 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 285 (accept_3_5 5 19 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 285 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 285 (accept_3_5 2 19 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 285 (Polychromatic418967fa.accept_10_1_9_5_1_83 1
  19 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 285))))))))))))))))))) (allB_succ 18
  285 (allA_succ_of_accept 17 18 285 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 18 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 16
  18 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 285 3 5 6 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 285
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 18 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 285 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 285 3 4 6 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 285
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 18 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 18 285 3 3 6 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 18 285 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 18 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 285 3 2 6 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 285
  (Polychromatic418967fa.accept_16_5_2_13_1_1007 5 18 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 18 285 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 18 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 18 285 3 1 6 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 18 285 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 18 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 285
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 285)))))))))))))))))) (allB_succ 17 285 (allA_succ_of_accept 16 17 285 (accept_3_4 16 17 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 285 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 17 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 285 (accept_3_4 13 17 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 285 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 17 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 285 (accept_3_4 10 17 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 17 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 285 (accept_3_4 7 17 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  285 (Polychromatic418967fa.accept_18_6_17_15_1_4603 6 17 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 285 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 285 (accept_3_4 4 17 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 285 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 285
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 285 (accept_3_4 1 17 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  285))))))))))))))))) (allB_succ 16 285 (allA_succ_of_accept 15 16 285 (Polychromatic418967fa.accept_11_4_5_10_1_926 15
  16 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 285 (accept_3_5 14 16
  285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 285 (Polychromatic418967fa.accept_6_1_4_3_1_14
  13 16 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 285
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 16 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 285 (accept_3_5 11 16 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 16 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 285 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 16 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 285 (accept_3_5 8 16 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 285
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 16 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 285 (accept_3_5 5 16 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  285 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 16 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 285 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 16 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 285 (accept_3_5 2 16 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 285)))))))))))))))) (allB_succ 15 285 (allA_succ_of_accept 14 15
  285 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 15 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 285 3 4 5 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 15 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 285 5 2 3 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 15 285 3 3 5 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 285
  (Polychromatic418967fa.accept_17_8_15_13_1_7942 8 15 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 285 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 15 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 285 3 2 5 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 285 5 1 3 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 285 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 285 3 1 5 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 285 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 15 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 285))))))))))))))) (allB_succ 14 285 (allA_succ_of_accept 13 14 285
  (accept_3_4 13 14 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 285
  (Polychromatic418967fa.accept_9_3_5_6_1_253 12 14 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 285 (accept_3_4 10 14 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 285 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 14 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 285 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  14 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 285 (accept_3_4 7 14 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 285 (Polychromatic418967fa.accept_10_6_4_5_1_615 6
  14 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 285 (accept_3_4 4 14 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 285 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 14 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 285 (accept_3_4 1 14 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 285)))))))))))))) (allB_succ 13 285 (allA_succ_of_accept 12 13 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 285 (accept_3_5 11 13 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 285 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 285 (Polychromatic418967fa.accept_21_9_13_12_1_10185 9 13 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 285 (accept_3_5 8 13 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 285 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 285
  (Polychromatic418967fa.accept_14_6_13_5_1_534 6 13 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 285 (accept_3_5 5 13 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  285 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 285 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 13 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 285 (accept_3_5 2 13 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 285 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 285))))))))))))) (allB_succ 12 285 (allA_succ_of_accept 11 12
  285 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 12 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 285 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 12 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 285 3 3 4 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 285 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 12 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 285
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 285 3 2 4 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 285 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 285 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 12 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 285 3 1 4 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 285
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 12 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 285 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 12 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 285)))))))))))) (allB_succ 11 285 (allA_succ_of_accept 10 11 285
  (accept_3_4 10 11 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 285
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 11 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 285 (accept_3_4 7 11 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 285 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  11 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 285 (accept_3_4 4 11 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 285 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  11 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 285 (accept_3_4 1 11 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  285))))))))))) (allB_succ 10 285 (allA_succ_of_accept 9 10 285 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 10 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 285 (accept_3_5 8 10 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 285
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 10 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 10 285 5 1 2 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 10 285 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 10 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 285 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 285 (accept_3_5 2 10 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 285 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 285)))))))))) (allB_succ 9 285
  (allA_succ_of_accept 8 9 285 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 9 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 285 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 9 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 285 3 2 3 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 285
  (Polychromatic418967fa.accept_16_5_9_13_1_3845 5 9 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 285 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 285 3 1 3 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 285 (Polychromatic418967fa.accept_21_2_9_12_1_4040 2 9 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 285
  (Polychromatic418967fa.accept_10_1_9_5_1_83 1 9 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 285))))))))) (allB_succ 8 285 (allA_succ_of_accept 7 8 285 (accept_3_4 7 8 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 285 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 8 285 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 285
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 285 (accept_3_4 4 8 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 285
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 8 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 285 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 8 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 285 (accept_3_4 1 8 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 285)))))))) (allB_succ 7 285 (allA_succ_of_accept 6 7 285
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 285 (accept_3_5 5 7 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 285
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 285 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 285 (accept_3_5 2 7 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 285 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 285))))))) (allB_succ 6 285 (allA_succ_of_accept 5 6 285
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 6 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 285 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 6 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 285 3 1 2 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 285 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 6 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 285
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 285)))))) (allB_succ 5 285 (allA_succ_of_accept 4 5 285 (accept_3_4 4 5 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 285 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 5 285 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 285 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 285 (accept_3_4 1 5 285
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 285))))) (allB_succ 4 285 (allA_succ_of_accept 3 4 285
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 4 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 285 (accept_3_5 2 4 285 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 285
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 285)))) (allB_succ 3 285 (allA_succ_of_accept 2 3 285 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 285
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 285
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 3 285 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 285))) (allB_succ 2 285 (allA_succ_of_accept 1 2 285 (accept_3_4 1 2 285 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 285)) (allB_two
  285))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


