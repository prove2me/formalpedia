-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch252_Segment000
-- name    : Polychromatic418967fa_Branch252_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:39:56.452322+00:00
-- url     : https://prove2.me/theorems/fd8826e7-58c3-4a0b-ac47-cec4b606c75e
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

def Polychromatic418967fa.branch_252_segment_000 : allB 101 252 :=
  allB_succ 100 252 (allA_succ_of_accept 99 100 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 99 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 100 252 2 49 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 100 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 97 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 100 252 4 24 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 100 252 (accept_3_5 95 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 100 252 2 47 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 100 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 93 100 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 100 252 4 23 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 100 252
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 91 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 100 252 2 45 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 100 252 (accept_3_5 89 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 100 252 4 22 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 100 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 87 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 100 252 2 43 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 100 252
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 85 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 100 252 4 21 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 100 252 (accept_3_5 83 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 100 252 2 41 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 100 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 81 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 252 4 20 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 79 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 252 2 39 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 252 (accept_3_5 77 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 252 4 19 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 100 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 75 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 100 252 2 37 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 252
  (Polychromatic418967fa.accept_15_13_10_12_1_2503 73 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 100 252 4 18 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 100 252 (accept_3_5 71 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 252 2 35 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 69 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 252 4 17 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 252
  (Polychromatic418967fa.accept_13_2_9_5_1_959 67 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 252 2 33 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 252 (accept_3_5 65 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 252 4 16 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 252 (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 252 2 31 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 252
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 61 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 100 252 4 15 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 100 252 (accept_3_5 59 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 252 2 29 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 57 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 252 4 14 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 55 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 252 2 27 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 252 (accept_3_5 53 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 252 4 13 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 51 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 252 2 25 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 252
  (Polychromatic418967fa.accept_16_1_4_12_1_376 49 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 252 4 12 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 252 (accept_3_5 47 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 252 2 23 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 252 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 252 4 11 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 252
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 43 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 252 2 21 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 252 (accept_3_5 41 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 252 4 10 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 252 2 19 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 252
  (Polychromatic418967fa.accept_15_7_10_12_1_2403 37 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 100 252 4 9 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 100 252 (accept_3_5 35 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 100 252 2 17 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 252 (Polychromatic418967fa.accept_16_1_4_12_1_376 33 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 252 4 8 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 31 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 252 2 15 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 252 (accept_3_5 29 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 252 4 7 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 100 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 100 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 252 2 13 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 252 (Polychromatic418967fa.accept_16_9_4_12_1_4896
  25 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 100 252 4 6 25 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 252
  (accept_3_5 23 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 252 2 11 50 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 252
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 100 252 4 5 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 100 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 19 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 252 2 9 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 252 (accept_3_5 17 100 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 252 4 4 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 252
  (Polychromatic418967fa.accept_13_2_9_5_1_959 15 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 100 252 2 7 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 100 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 252 4 3 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 252 (accept_3_5 11 100 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 252 2 5 50 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 252 4 2 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 100 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 252 2 3 50 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 252 (accept_3_5 5 100 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100 252 4 1 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 100 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 100 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 252 2 1 50 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 252
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 100 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 99 252 (allA_succ_of_accept 98 99 252 (Polychromatic418967fa.accept_23_6_7_22_1_15275 98 99 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 97 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 252 3 32 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 95 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 94 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 252 3 31 33 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 252
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 92 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 91 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 252 9 10 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498
  89 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 252
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 88 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 252 3 29 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 252 (Polychromatic418967fa.accept_27_5_18_9_1_15274 86 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 252 (Polychromatic418967fa.accept_15_10_9_12_1_2497 85 99
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 252 3 28 33 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 252
  (Polychromatic418967fa.accept_25_8_24_2_1_15273 83 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 252 (Polychromatic418967fa.accept_19_6_4_5_1_5650 82 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 252 9 9 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 80 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 79 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 252 3 26 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 77 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 252 (Polychromatic418967fa.accept_25_1_24_2_1_15272 76 99
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 252 3 25 33 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 252
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 74 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 252 (Polychromatic418967fa.accept_16_9_3_12_1_1802 73 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 252 9 8 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 252
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 70 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 252 3 23 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 68 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 67 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 252 3 22 33 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 65 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 64 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 252 9 7 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 62 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 61 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 252 3 20 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 252 (Polychromatic418967fa.accept_16_10_3_12_1_1758 58 99
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 252 3 19 33 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 252
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 56 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 252 9 6 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 53 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 252
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 52 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 252 3 17 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 50 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 99
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 252 3 16 33 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 252 (Polychromatic418967fa.accept_19_8_4_5_1_8569 46 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 252 9 5 11 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498 44 99
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 252
  (Polychromatic418967fa.accept_22_21_11_10_1_12218 43 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 99 252 3 14 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 99 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 41 99 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 252
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 40 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 99 252 3 13 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 99 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 38 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 252 9 4 11 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 35 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 34 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 252 3 11 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 252 (Polychromatic418967fa.accept_25_7_24_2_1_15271
  32 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 99 252 3 10 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 99 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 29 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 252 (Polychromatic418967fa.accept_19_9_4_5_1_3019 28 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 252 9 3 11 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 252
  (Polychromatic418967fa.accept_16_10_3_12_1_1758 26 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 25 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 252 3 8 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 252
  (Polychromatic418967fa.accept_20_2_19_12_1_2500 22 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 99 252 3 7 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 99 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 99
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 252 9 2 11 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 16 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 252 3 5 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 14 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 252
  (Polychromatic418967fa.accept_20_13_19_12_1_5143 13 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 99 252 3 4 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 99 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 99 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616
  10 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 252 9 1 11 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 252
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 252 3 2 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 252
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 99 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 99 252 3 1 33 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 99 252 (Polychromatic418967fa.accept_19_2_4_5_1_3021 2 99 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 99 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  252 (allA_succ_of_accept 97 98 252 (accept_3_4 97 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 252 2 48 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 95 98 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 252 2 47 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189
  93 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 252 2 46 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 91 98 252 7 13 14 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 90 98 252 2 45 49
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 252
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 89 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 252 2 44 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 252 (Polychromatic418967fa.accept_16_7_2_12_1_1754 87 98 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 252 2 43 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 252 (accept_3_4 85 98 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 252 14 6 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 252 (Polychromatic418967fa.accept_19_7_3_5_1_8585 83 98 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 252 2 41 49 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 252
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 81 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 252 2 40 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 252 (accept_3_4 79 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 252 2 39 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 98 252 7 11 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 98 252 2 38 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 98 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 75 98 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 98 252 2 37 49 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 98 252 (accept_3_4 73 98 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 98 252 2 36 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 98 252
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 71 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 98 252 14 5 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 98 252 (Polychromatic418967fa.accept_17_1_13_14_1_478 69 98 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 98 252 2 34 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 98 252 (accept_3_4 67 98 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 98 252 2 33 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 98 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 98 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 252 2 32 49 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 98 252 7 9 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 98 252 2 31 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 98 252
  (accept_3_4 61 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 98 252 2 30 49 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 98 252
  (Polychromatic418967fa.accept_19_2_3_5_1_5721 59 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 98 252 2 29 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 98 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800 57 98 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 252 14 4 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 252 (accept_3_4 55 98 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98 252 2 27 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 98 252 (Polychromatic418967fa.accept_23_7_6_22_1_15270 53 98
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 252 2 26 49 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 252
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 51 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 252 2 25 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 98 252 7 7 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 98 252 2 24 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 98 252 (Polychromatic418967fa.accept_16_15_2_12_1_1799 47 98 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 252 2 23 49 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 252 2 22 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 252 (accept_3_4 43 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 252 14 3 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 98 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 41 98 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 252 2 20 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 252 (Polychromatic418967fa.accept_16_7_2_12_1_1754
  39 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 252 2 19 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 252
  (accept_3_4 37 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 252 2 18 49 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 98 252 7 5 14 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 98 252 2 17 49 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 252
  (Polychromatic418967fa.accept_15_3_8_12_1_900 33 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 252 2 16 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 252 (accept_3_4 31 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 252 2 15 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 252 (Polychromatic418967fa.accept_19_10_3_5_1_11346 29 98 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 252 14 2 7 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 252
  (Polychromatic418967fa.accept_17_10_13_14_1_3094 27 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 98 252 2 13 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 98 252 (accept_3_4 25 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 252 2 12 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 252 (Polychromatic418967fa.accept_16_7_2_12_1_1754 23 98 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 252 2 11 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 98 252 7 3 14 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 98 252 2 10 49 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 252 (accept_3_4 19 98 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 252 2 9 49 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 252
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 17 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 98 252 2 8 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 98 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 98 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 252 14 1 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 252 (accept_3_4 13 98 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 98 252 2 6 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 98 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 98 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 252 2 5 49 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 252
  (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 98 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 98 252 2 4 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 98 252 7 1 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 98 252 2 3 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 98 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 98 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 252 2 2 49 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 98 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 252 2 1 49 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 252 (accept_3_4 1 98 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  252 (allA_succ_of_accept 96 97 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 96 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 252 (accept_3_5 95 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 97 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 94 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 93 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 97 252 (accept_3_5 92 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  97 252 (Polychromatic418967fa.accept_16_11_1_12_1_1795 91 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 97 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 90 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 252 (accept_3_5 89 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 97 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 88 97
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 252
  (Polychromatic418967fa.accept_20_7_17_12_1_11156 87 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 97 252 (accept_3_5 86 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 97 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 85 97 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 97 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 252 (accept_3_5 83 97 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 97 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333
  82 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 252
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 81 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 252 (accept_3_5 80 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 79 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 78 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 252 (accept_3_5 77 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 76 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 75 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 252 (accept_3_5 74 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 252 (Polychromatic418967fa.accept_19_16_2_5_1_5681 73 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 252 (Polychromatic418967fa.accept_16_8_1_12_1_984 72 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 252 (accept_3_5 71 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 252 (Polychromatic418967fa.accept_15_10_7_12_1_2490 70 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 252 (accept_3_5 68 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 67 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 66 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 252 (accept_3_5 65 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 252
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 252 (accept_3_5 62 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 252 (Polychromatic418967fa.accept_17_9_12_14_1_5423 60 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 252 (accept_3_5 59 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 252 (Polychromatic418967fa.accept_48_10_1_12_1_15269 58 97
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 252
  (Polychromatic418967fa.accept_22_13_9_10_1_15235 57 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 97 252 (accept_3_5 56 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 97 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 97 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 97 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 252 (accept_3_5 53 97 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 252 (Polychromatic418967fa.accept_11_8_9_10_1_503
  52 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 252
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 252 (accept_3_5 50 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 48 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 252 (accept_3_5 47 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 252 (Polychromatic418967fa.accept_19_8_2_5_1_5678 46 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 45 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 252 (accept_3_5 44 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 43 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 42 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 252 (accept_3_5 41 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 40 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 39 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 252 (accept_3_5 38 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 252 (accept_3_5 35 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 97 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 252
  (Polychromatic418967fa.accept_15_3_7_12_1_372 33 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 252 (accept_3_5 32 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 252 (Polychromatic418967fa.accept_25_6_22_2_1_15268 31 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 252 (accept_3_5 29 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 252 (Polychromatic418967fa.accept_17_11_12_14_1_5431 28 97 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 252
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 252 (accept_3_5 26 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 252 (accept_3_5 23 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 252 (Polychromatic418967fa.accept_19_3_2_5_1_5679 22 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 252 (accept_3_5 20 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 18 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 252 (accept_3_5 17 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 16 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 15 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 252 (accept_3_5 14 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 252 (accept_3_5 11 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 9 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 252 (accept_3_5 8 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  252 (Polychromatic418967fa.accept_19_7_2_5_1_5680 7 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 6 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 252 (accept_3_5 5 97 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 97 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 252
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 252 (accept_3_5 2 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  252 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 97 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 97
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 252
  (allA_succ_of_accept 95 96 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 95 96 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96 252 2 47 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 96 252 3 31 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 96 252 4 23 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 91
  96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 252 6 15 16 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 252
  (Polychromatic418967fa.accept_25_14_21_2_1_15201 89 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 96 252 4 22 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 96 252 3 29 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 96 252 2 43 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 96 252 (Polychromatic418967fa.accept_15_10_6_12_1_1645 85 96
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 252 12 7 8 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 252
  (Polychromatic418967fa.accept_25_8_21_2_1_8188 83 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 96 252 2 41 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 96 252 3 27 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 96 252 4 20 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 96 252 (Polychromatic418967fa.accept_19_3_1_5_1_8549 79 96 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 252 6 13 16 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 252
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 77 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 252 4 19 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 75 96 252 3 25 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 96 252 2 37 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 96 252 (Polychromatic418967fa.accept_19_16_1_5_1_3084 73 96 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 252 12 6 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 71
  96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 252 2 35 48 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 96 252 3 23 32 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 96 252 4 17 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 67 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 252 6 11 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 65 96 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 252 4 16 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 96 252 3 21 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 96 252 2 31 48 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 61 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 252 12 5 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 252 (Polychromatic418967fa.accept_17_8_11_14_1_6770 59 96 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 252 2 29 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 96 252 3 19 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 96 252 4 14 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 252 (Polychromatic418967fa.accept_15_10_6_12_1_1645
  55 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 252 6 9 16 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 252
  (Polychromatic418967fa.accept_11_9_8_10_1_934 53 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 252 4 13 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 96 252 3 17 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 96 252 2 25 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 96 252 (Polychromatic418967fa.accept_22_5_8_10_1_12151 49 96 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 252 12 4 8 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 252
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 47 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 96 252 2 23 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 96 252 3 15 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 96 252 4 11 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 96 252 (Polychromatic418967fa.accept_25_18_21_2_1_15267 43 96 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 252 6 7 16 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 252 4 10 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 96 252 3 13 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 96 252 2 19 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 96 252 (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 96 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 252 12 3 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 252 (Polychromatic418967fa.accept_15_5_6_12_1_916
  35 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 252 2 17 48 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 96 252 3 11 32 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 96 252 4 8 24 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 252 6 5 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 252 (Polychromatic418967fa.accept_17_12_11_14_1_3120 29 96 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 252 4 7 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 96 252 3 9 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 96 252 2 13 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 252 (Polychromatic418967fa.accept_15_10_6_12_1_1645
  25 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 252 12 2 8 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 252
  (Polychromatic418967fa.accept_19_4_1_5_1_9933 23 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 96 252 2 11 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 96 252 3 7 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 96 252 4 5 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 252 (Polychromatic418967fa.accept_22_19_8_10_1_12142 19 96 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 252 6 3 16 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 252
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 96 252 4 4 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 96 252 3 5 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 96 252 2 7 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 252 (Polychromatic418967fa.accept_27_13_15_9_1_15266 13 96 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 252 12 1 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 96 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 252 2 5 48 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 96 252 3 3 32 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 96 252 4 2 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 96 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 252 6 1 16 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 96 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 252 4 1 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 96 252 3 1 32 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 252 2 1 48 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 96 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 252
  (allA_succ_of_accept 94 95 252 (accept_3_4 94 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 93 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 92 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 252 (accept_3_4 91 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 90 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 252
  (Polychromatic418967fa.accept_23_20_3_22_1_15265 89 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 95 252 (accept_3_4 88 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 95 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 87 95 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 252 (Polychromatic418967fa.accept_17_1_10_14_1_1173 86 95
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 252 (accept_3_4 85 95 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330
  84 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 83 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 252 (accept_3_4 82 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 81 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 80 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 252 (accept_3_4 79 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 77 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 252 (accept_3_4 76 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 74 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 252 (accept_3_4 73 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 72 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 71 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 252 (accept_3_4 70 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 69 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 68 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 252 (accept_3_4 67 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 66 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 252
  (Polychromatic418967fa.accept_20_5_15_12_1_9720 65 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 252 (accept_3_4 64 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 62 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 252 (accept_3_4 61 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 252 (Polychromatic418967fa.accept_22_16_7_10_1_7356 60 95
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 252 (accept_3_4 58 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 56 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 252 (accept_3_4 55 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 54 95 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 53 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 252 (accept_3_4 52 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744 50 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 252 (accept_3_4 49 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 95 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 47 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 252 (accept_3_4 46 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 252 (Polychromatic418967fa.accept_24_20_23_12_1_8488 44 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 252 (accept_3_4 43 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 252 (Polychromatic418967fa.accept_23_19_3_22_1_13660 42 95
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 252
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 41 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 252 (accept_3_4 40 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 252 (accept_3_4 37 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 252 (accept_3_4 34 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 32 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 252 (accept_3_4 31 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 252 (Polychromatic418967fa.accept_17_13_10_14_1_4211 30 95 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 252
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 29 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 95 252 (accept_3_4 28 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 95 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 95 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 252 (Polychromatic418967fa.accept_20_6_15_12_1_6637 26 95
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 252 (accept_3_4 25 95 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640
  24 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 252 (accept_3_4 22 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 252 (Polychromatic418967fa.accept_16_4_15_12_1_1745 20 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 252 (accept_3_4 19 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 95 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 252 (accept_3_4 16 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 252 (accept_3_4 13 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 252 (accept_3_4 10 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 252 (accept_3_4 7 95 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 95 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 252
  (Polychromatic418967fa.accept_17_5_10_14_1_2083 5 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 252 (accept_3_4 4 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 95 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 95 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 252 (accept_3_4 1 95 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 252
  (allA_succ_of_accept 93 94 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 93 94 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 94 252 2 46 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 94 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401
  91 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 252 2 45 47 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 252
  (accept_3_5 89 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 252 2 44 47 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 87 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 94 252 2 43 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 94 252 (Polychromatic418967fa.accept_19_9_18_5_1_7101 85 94 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 94 252 2 42 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 94 252 (accept_3_5 83 94 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 94 252 2 41 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 94 252
  (Polychromatic418967fa.accept_22_15_6_10_1_12166 81 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 94 252 2 40 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 94 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 79 94 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 94 252 2 39 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 94 252 (accept_3_5 77 94 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 94 252 2 38 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 94 252
  (Polychromatic418967fa.accept_27_21_13_9_1_13383 75 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 94 252 2 37 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 94 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 73 94 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 94 252 2 36 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 94 252 (accept_3_5 71 94 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 94 252 2 35 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 94 252
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 69 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 94 252 2 34 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 94 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 67 94 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 94 252 2 33 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 94 252 (accept_3_5 65 94 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 94 252 2 32 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 94 252 (Polychromatic418967fa.accept_13_11_3_5_1_982
  63 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 252 2 31 47 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 252
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 61 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 252 2 30 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 94 252 (accept_3_5 59 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 94 252 2 29 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 94 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 94 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 252 2 28 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 252
  (Polychromatic418967fa.accept_17_4_9_14_1_5406 55 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 252 2 27 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 94 252 (accept_3_5 53 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 94 252 2 26 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 94 252 (Polychromatic418967fa.accept_19_13_18_5_1_8619 51 94 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 252 2 25 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 252 2 24 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 94 252 (accept_3_5 47 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 94 252 2 23 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 94 252 (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 94 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 252 2 22 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 252
  (Polychromatic418967fa.accept_22_21_6_10_1_4188 43 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 252 2 21 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 94 252 (accept_3_5 41 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 94 252 2 20 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 94 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 252 2 19 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 252 2 18 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 94 252 (accept_3_5 35 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 94 252 2 17 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 252 (Polychromatic418967fa.accept_25_8_19_2_1_15264 33 94 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 252 2 16 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 252
  (Polychromatic418967fa.accept_15_1_4_12_1_2401 31 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 252 2 15 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 94 252 (accept_3_5 29 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 252 2 14 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 94 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 94 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 252 2 13 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 252
  (Polychromatic418967fa.accept_19_6_18_5_1_5630 25 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 252 2 12 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 94 252 (accept_3_5 23 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 94 252 2 11 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 94 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 94 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 252 2 10 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 252
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 252 2 9 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 252 (accept_3_5 17 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  252 2 8 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 252 2 7 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 94 252 (Polychromatic418967fa.accept_19_13_18_5_1_8619 13 94 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 252 2 6 47 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 252 (accept_3_5 11 94 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 252 2 5 47 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 252
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 252 2 4 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 94 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 252 2 3 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 252 (accept_3_5 5 94 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 252 2 2 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 252 (Polychromatic418967fa.accept_22_3_6_10_1_15263 3 94 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 252 2 1 47 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 1
  94 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 252
  (allA_succ_of_accept 92 93 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 92 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 91 93 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 252 3 30 31 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 89 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 88 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 252 3 29 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 252
  (Polychromatic418967fa.accept_23_17_1_22_1_15262 86 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 93 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 85 93 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 93 252 3 28 31 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 93 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 83 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 93 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 82 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 252 3 27 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 252 (Polychromatic418967fa.accept_25_5_18_2_1_13572
  80 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 93 252
  (Polychromatic418967fa.accept_16_15_13_12_1_1787 79 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 93 252 3 26 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 93 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 77 93 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 252
  (Polychromatic418967fa.accept_23_7_1_22_1_15202 76 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 252 3 25 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 74 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 93 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 252 3 24 31 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 71 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 70 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 252 3 23 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632
  68 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 67 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 252 3 22 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 64 93
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 252 3 21 31 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 252
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 62 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 61 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 252 3 20 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 252 (Polychromatic418967fa.accept_11_4_5_10_1_926
  59 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 58 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 252 3 19 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 56 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 93 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 252 3 18 31 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 252
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 53 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 52 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 252 3 17 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724
  50 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 49 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 252 3 16 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 47 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 252 (Polychromatic418967fa.accept_13_7_2_5_1_2344 46 93 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 252 3 15 31 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 252
  (Polychromatic418967fa.accept_23_21_1_22_1_15261 44 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 93 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 43 93 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 252 3 14 31 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 252 (Polychromatic418967fa.accept_16_8_13_12_1_3809 40 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 252 3 13 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634
  38 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 37 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 93 252 3 12 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 93 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 252 (Polychromatic418967fa.accept_19_15_17_5_1_3052 34 93
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 252 3 11 31 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 252
  (Polychromatic418967fa.accept_15_2_3_12_1_891 32 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 252 3 10 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632
  29 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 28 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 93 252 3 9 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 93 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 93 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 252 3 8 31 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 252
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 22 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 252 3 7 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 252 (Polychromatic418967fa.accept_13_7_2_5_1_2344 20 93 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 252
  (Polychromatic418967fa.accept_20_19_13_12_1_2476 19 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 93 252 3 6 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 93 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 93 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632
  16 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 252 3 5 31 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 252
  (Polychromatic418967fa.accept_19_14_17_5_1_15232 14 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 93 252 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 93 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 252 3 4 31 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 252 3 3 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 93 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 252
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 7 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 93 252 3 2 31 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 93 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 93 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 252 3 1 31 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 252
  (Polychromatic418967fa.accept_15_2_3_12_1_891 2 93 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 93 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 252
  (allA_succ_of_accept 91 92 252 (accept_3_4 91 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  252 2 45 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 252 (Polychromatic418967fa.accept_15_14_2_12_1_2472 89 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 252 4 22 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 87 92 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 252 2 43 46 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 252 (accept_3_4 85 92 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 252 4 21 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 252
  (Polychromatic418967fa.accept_22_17_4_10_1_7339 83 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 252 2 41 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 81 92 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 252 4 20 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 252 (accept_3_4 79 92 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 252 2 39 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 252 (Polychromatic418967fa.accept_13_12_1_5_1_1650
  77 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 252 4 19 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 252
  (Polychromatic418967fa.accept_27_21_11_9_1_13403 75 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 92 252 2 37 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 92 252 (accept_3_4 73 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 252 4 18 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 92 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 71 92 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 252 2 35 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628
  69 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 252 4 17 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 252 (accept_3_4 67
  92 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 252 2 33 46 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 252
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 65 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 252 4 16 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 63 92 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 252 2 31 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 252 (accept_3_4 61 92 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 252 4 15 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 252 (Polychromatic418967fa.accept_15_14_2_12_1_2472 59 92
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 252 2 29 46 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 252
  (Polychromatic418967fa.accept_17_6_7_14_1_6704 57 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 252 4 14 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 252 (accept_3_4 55 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  252 2 27 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 92 252 (Polychromatic418967fa.accept_24_5_20_12_1_11905 53 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 252 4 13 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 252 (Polychromatic418967fa.accept_13_12_1_5_1_1650 51 92 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 252 2 25 46 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 252 (accept_3_4 49 92 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 252 4 12 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 252
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 47 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 252 2 23 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 92 252 (Polychromatic418967fa.accept_13_6_1_5_1_3988 45 92 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 252 4 11 23 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 252 (accept_3_4 43 92 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 252 2 21 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 252 (Polychromatic418967fa.accept_19_3_16_5_1_7098
  41 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 252 4 10 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 252
  (Polychromatic418967fa.accept_19_1_16_5_1_5671 39 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 252 2 19 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 92 252 (accept_3_4 37 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 252 4 9 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 92 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 35 92 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 252 2 17 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469
  33 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 252 4 8 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 252 (accept_3_4 31
  92 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 252 2 15 46 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 252
  (Polychromatic418967fa.accept_13_3_1_5_1_499 29 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 252 4 7 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 92 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 252 2 13 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 252 (accept_3_4 25 92 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 252 4 6 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 92 252 (Polychromatic418967fa.accept_17_6_7_14_1_6704 23 92 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 252 2 11 46 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 252
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 252 4 5 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 252 (accept_3_4 19 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  252 2 9 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 252 4 4 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 252 (Polychromatic418967fa.accept_22_15_4_10_1_12149 15 92 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 252 2 7 46 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 252 (accept_3_4 13 92 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 252 4 3 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 252 (Polychromatic418967fa.accept_19_11_16_5_1_5667
  11 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 252 2 5 46 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 252
  (Polychromatic418967fa.accept_13_9_1_5_1_964 9 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 252 4 2 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 252 (accept_3_4 7 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 252
  2 3 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  252 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 92 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 92 252 4 1 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 92 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 92 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 252 2 1 46 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 252 (accept_3_4 1 92 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 92
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 252
  (allA_succ_of_accept 90 91 252 (Polychromatic418967fa.accept_16_10_11_12_1_4835 90 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 252 (accept_3_5 89 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 88 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 87 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 91 252 (accept_3_5 86 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  91 252 (Polychromatic418967fa.accept_19_9_15_5_1_5666 85 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 91 252 7 12 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 91 252 (accept_3_5 83 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 91 252 (Polychromatic418967fa.accept_19_6_15_5_1_5697 82 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 252 (Polychromatic418967fa.accept_16_1_11_12_1_1774 81 91
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 252 (accept_3_5 80 91 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 79
  91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 252
  (Polychromatic418967fa.accept_24_6_19_12_1_11904 78 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 91 252 7 11 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 91 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 76 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 252
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 75 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 91 252 (accept_3_5 74 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  91 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 73 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 252 (Polychromatic418967fa.accept_16_8_11_12_1_962 72 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 252 (accept_3_5 71 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 91 252 7 10 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 91 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 69
  91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 252 (accept_3_5 68 91
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 252
  (Polychromatic418967fa.accept_19_10_15_5_1_5698 67 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 91 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 252 (accept_3_5 65 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 91 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 64 91 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 91 252 7 9 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 91 252 (accept_3_5 62 91 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 252 (Polychromatic418967fa.accept_19_4_15_5_1_3043 61 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 252
  (Polychromatic418967fa.accept_22_16_3_10_1_5739 60 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 252 (accept_3_5 59 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 58 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 252 (Polychromatic418967fa.accept_22_13_3_10_1_15260 57 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 91 252 7 8 13 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 91 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 55 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 91 252 (Polychromatic418967fa.accept_17_3_6_14_1_4312 54 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 252 (accept_3_5 53 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 91 252 (Polychromatic418967fa.accept_16_4_11_12_1_1775 52 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 252 (accept_3_5 50 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 91
  252 7 7 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  91 252 (Polychromatic418967fa.accept_19_10_15_5_1_5698 48 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 91 252 (accept_3_5 47 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 91 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 252 (Polychromatic418967fa.accept_24_21_19_12_1_8486 45 91
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 252 (accept_3_5 44 91 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 252 (Polychromatic418967fa.accept_10_3_1_2_1_521
  43 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 91 252 7 6 13 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 91 252 (accept_3_5 41
  91 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 40 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 91 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 252 (accept_3_5 38 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 91 252 (Polychromatic418967fa.accept_17_3_6_14_1_4312 37 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 91 252 7 5 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 91 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 34 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 91 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 252 (accept_3_5 32 91 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31
  91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 252
  (Polychromatic418967fa.accept_19_11_15_5_1_5699 30 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 252 (accept_3_5 29 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91
  252 7 4 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  91 252 (Polychromatic418967fa.accept_30_27_1_12_1_15259 27 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 91 252 (accept_3_5 26 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 91 252 (Polychromatic418967fa.accept_17_8_6_14_1_6718 25 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 252 (Polychromatic418967fa.accept_16_8_11_12_1_962 24 91
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 252 (accept_3_5 23 91 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 252
  (Polychromatic418967fa.accept_27_22_10_9_1_9620 22 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 91 252 7 3 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 91 252 (accept_3_5 20 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 252 (accept_3_5 17 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 91 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 91 252 7 2 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 91 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 91 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 252 (Polychromatic418967fa.accept_19_12_15_5_1_8600 12 91
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 252 (accept_3_5 11 91 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 252
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 10 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 91 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 252 (accept_3_5 8 91 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 252 7 1 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 91 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 252 (accept_3_5 5 91 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 91 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 3 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 252 (accept_3_5 2 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  252 (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 91 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 252
  (allA_succ_of_accept 89 90 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 89 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90 252 2 44 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 90 252 3 29 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 90 252 2 43 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 252
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 85 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 90 252 6 14 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 252 (Polychromatic418967fa.accept_16_3_10_12_1_4814 83 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 252 2 41 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 90 252 9 9 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 90 252 2 40 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 252
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 79 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 252 6 13 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 90 252 (Polychromatic418967fa.accept_16_13_10_12_1_1811 77 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 252 2 38 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 90 252 3 25 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 90 252 2 37 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 252
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 73 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 252 18 4 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 71 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 252 2 35 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 90 252 3 23 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 90 252 2 34 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 67 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 252 6 11 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 90 252 (Polychromatic418967fa.accept_19_8_14_5_1_9919 65 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 252 2 32 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 90 252 9 7 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 90 252 2 31 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 252
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 61 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 90 252 6 10 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 90 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603 59 90 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 252 2 29 45 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 90 252 3 19 30 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 90 252 2 28 45 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 252
  (Polychromatic418967fa.accept_19_17_14_5_1_8561 55 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 252 18 3 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 53 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 252 2 26 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 90 252 3 17 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 90 252 2 25 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 252
  (Polychromatic418967fa.accept_19_11_14_5_1_5629 49 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 252 6 8 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 90 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 47 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 252 2 23 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 252 9 5 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 252 2 22 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 252
  (Polychromatic418967fa.accept_13_4_12_5_1_476 43 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 252 6 7 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 252 (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 252 2 20 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 90 252 3 13 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 90 252 2 19 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 252
  (Polychromatic418967fa.accept_16_5_10_12_1_4904 37 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 252 18 2 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 252 (Polychromatic418967fa.accept_16_3_10_12_1_4814 35 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 252 2 17 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 252 3 11 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 252 2 16 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 252
  (Polychromatic418967fa.accept_24_7_18_12_1_15258 31 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 90 252 6 5 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 252 (Polychromatic418967fa.accept_16_13_10_12_1_1811 29 90 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 252 2 14 45 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 90 252 9 3 10 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 90 252 2 13 45 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 252
  (Polychromatic418967fa.accept_19_6_14_5_1_4339 25 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 252 6 4 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 252 2 11 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 90 252 3 7 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 252 2 10 45 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 252 18 1 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 252 2 8 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 252 3 5 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 252 2 7 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 252
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 90 252 6 2 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 90 252 (Polychromatic418967fa.accept_16_11_10_12_1_4832 11 90 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 252 2 5 45 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 90 252 9 1 10 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 90 252 2 4 45 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 252
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 90 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 252 6 1 15 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 252 (Polychromatic418967fa.accept_16_5_10_12_1_4904 5 90 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 252 2 2 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 90 252 3 1 30 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 252 2 1 45 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 90 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 252
  (allA_succ_of_accept 88 89 252 (accept_3_4 88 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 87 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 86 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 252 (accept_3_4 85 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 84 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 252
  (Polychromatic418967fa.accept_16_3_9_12_1_4831 83 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 252 (accept_3_4 82 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 81 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 252 (Polychromatic418967fa.accept_22_14_1_10_1_5736 80 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 252 (accept_3_4 79 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 252 (Polychromatic418967fa.accept_24_6_17_12_1_6681 78 89
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 77 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 252 (accept_3_4 76 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 75 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 252 (Polychromatic418967fa.accept_27_20_8_9_1_15257 74 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 252 (accept_3_4 73 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 72 89
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 71 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 252 (accept_3_4 70 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 68 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 252 (accept_3_4 67 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 252 (Polychromatic418967fa.accept_16_2_9_12_1_46 66 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 252
  (Polychromatic418967fa.accept_19_8_13_5_1_1889 65 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 252 (accept_3_4 64 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 252 (Polychromatic418967fa.accept_20_3_9_12_1_6671 63 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 252 (Polychromatic418967fa.accept_15_2_14_12_1_2453 62 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 252 (accept_3_4 61 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 252 (Polychromatic418967fa.accept_17_9_4_14_1_4302 60 89
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 252
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 59 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 252 (accept_3_4 58 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 56 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 252 (accept_3_4 55 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 54 89
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 53 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 252 (accept_3_4 52 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 252 (Polychromatic418967fa.accept_16_2_9_12_1_46 50 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 252 (accept_3_4 49 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 252 (Polychromatic418967fa.accept_19_10_13_5_1_3091 48 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 252 (accept_3_4 46 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 252 (Polychromatic418967fa.accept_23_21_20_22_1_15256 44 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 252 (accept_3_4 43 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 89 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 252 (accept_3_4 40 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 252 (Polychromatic418967fa.accept_25_13_14_2_1_9995 38 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 252 (accept_3_4 37 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 252 (Polychromatic418967fa.accept_16_4_9_12_1_4829 36 89
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 35 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 252 (accept_3_4 34 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 32 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 252 (accept_3_4 31 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 252 (Polychromatic418967fa.accept_17_13_4_14_1_4272 30 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 252 (accept_3_4 28 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 252 (accept_3_4 25 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 89 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 252
  (Polychromatic418967fa.accept_20_3_9_12_1_6671 23 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 252 (accept_3_4 22 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 252 (accept_3_4 19 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 252 (Polychromatic418967fa.accept_16_2_9_12_1_46 18 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 252 (accept_3_4 16 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 252 (Polychromatic418967fa.accept_24_15_17_12_1_662 15 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 252 (Polychromatic418967fa.accept_19_14_13_5_1_9905 14 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 252 (accept_3_4 13 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 252 (Polychromatic418967fa.accept_19_12_13_5_1_11331 12 89
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 252 (accept_3_4 10 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 252 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 252 (accept_3_4 7 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 89 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 252 (accept_3_4 4 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 89 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 2 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 252 (accept_3_4 1 89 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 252
  (allA_succ_of_accept 87 88 252 (Polychromatic418967fa.accept_16_7_8_12_1_4902 87 88 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 88 252 2 43 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 88 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 85
  88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 88 252 4 21 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 88 252 (accept_3_5 83
  88 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88 252 2 41 44 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 88 252
  (Polychromatic418967fa.accept_16_1_8_12_1_405 81 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 88 252 4 20 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 88 252 (Polychromatic418967fa.accept_16_15_8_12_1_2737 79 88 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 88 252 2 39 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 88 252 (accept_3_5 77 88 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 88 252 4 19 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 88 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 75 88 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 88 252 2 37 44 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 88 252
  (Polychromatic418967fa.accept_13_8_10_5_1_977 73 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 88 252 4 18 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 88 252 (accept_3_5 71 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88
  252 2 35 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  69 88 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 69 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 88 252 4 17 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 88 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 67 88 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 88 252 2 33 44 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 88 252 (accept_3_5 65 88 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88 252 4 16 22 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 88 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 63 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 88 252 2 31 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 88 252 (Polychromatic418967fa.accept_15_1_13_12_1_347 61 88 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 88 252 4 15 22 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 252 (accept_3_5 59 88 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88 252 2 29 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 88 252 (Polychromatic418967fa.accept_16_9_8_12_1_979
  57 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 88 252 4 14 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 88 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 55 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 88 252 2 27 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 88 252 (accept_3_5 53 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 88 252 4 13 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 88 252 (Polychromatic418967fa.accept_16_3_8_12_1_2736 51 88 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 252 2 25 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 252 (Polychromatic418967fa.accept_16_1_8_12_1_405
  49 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 252 4 12 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 252 (accept_3_5 47
  88 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 252 2 23 44 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 88 252 4 11 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 43 88 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 252 2 21 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 252 (accept_3_5 41 88 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 252 4 10 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 252 (Polychromatic418967fa.accept_16_7_8_12_1_4902 39 88 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 252 2 19 44 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 252
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 37 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 252 4 9 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 252 (accept_3_5 35 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  252 2 17 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 88 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 33 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 252 4 8 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 88 252 (Polychromatic418967fa.accept_15_1_13_12_1_347 31 88 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 252 2 15 44 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 252 (accept_3_5 29 88 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 252 4 7 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 252 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 88
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 252 2 13 44 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 252 4 6 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 252 (accept_3_5 23 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  252 2 11 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 88 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 21 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 252 4 5 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 88 252 (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 88 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 252 2 9 44 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 252 (accept_3_5 17 88 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 252 4 4 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 88 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 88 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 252 2 7 44 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 252
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 13 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 252 4 3 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 252 (accept_3_5 11 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  252 2 5 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 252 (Polychromatic418967fa.accept_16_9_8_12_1_979 9 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 252 4 2 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 252 (Polychromatic418967fa.accept_16_7_8_12_1_4902 7 88 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 252 2 3 44 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 252 (accept_3_5 5 88 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 252 4 1 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 88 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 252 2 1 44 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 252
  (Polychromatic418967fa.accept_15_1_13_12_1_347 1 88 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  252 (allA_succ_of_accept 86 87 252 (Polychromatic418967fa.accept_19_10_11_5_1_7093 86 87 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 252 (Polychromatic418967fa.accept_10_5_7_2_1_516
  85 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 252 3 28 29 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 83 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 82 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 252 3 27 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 80
  87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 79 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 252 3 26 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 252 (Polychromatic418967fa.accept_20_17_7_12_1_6632 77 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 252 (Polychromatic418967fa.accept_25_1_12_2_1_13539 76 87
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 252 3 25 29 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 74 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 252 (Polychromatic418967fa.accept_17_5_2_14_1_4270 73 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 252 3 24 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 252 (Polychromatic418967fa.accept_17_3_2_14_1_6714
  71 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 252
  (Polychromatic418967fa.accept_19_13_11_5_1_5692 70 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 252 3 23 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 68 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 87 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 252 3 22 29 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 65 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 252 3 21 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 252 (Polychromatic418967fa.accept_20_2_7_12_1_5215
  62 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 252
  (Polychromatic418967fa.accept_22_17_21_10_1_5733 61 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 87 252 3 20 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 87 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 87 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 252
  (Polychromatic418967fa.accept_22_14_21_10_1_13737 58 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 87 252 3 19 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 87 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 56 87 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 55 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 87 252 3 18 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 87 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 53 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 252 (Polychromatic418967fa.accept_16_4_7_12_1_2734 52 87
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 87 252 3 17 29 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 87 252
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 50 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 252 3 16 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 252
  (Polychromatic418967fa.accept_22_3_21_10_1_15255 47 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 87 252 (Polychromatic418967fa.accept_20_6_7_12_1_8197 46 87 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 252 3 15 29 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 252 3 14 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 41
  87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 252
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 40 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 87 252 3 13 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 87 252 (Polychromatic418967fa.accept_26_12_9_18_1_15254 38 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 252 (Polychromatic418967fa.accept_16_5_7_12_1_7206 37 87
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 252 3 12 29 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 252 3 11 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 252 (Polychromatic418967fa.accept_19_13_11_5_1_5692
  32 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 252
  (Polychromatic418967fa.accept_19_12_11_5_1_950 31 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 87 252 3 10 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 87 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 28 87 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 252 3 9 29 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 252
  (Polychromatic418967fa.accept_20_6_7_12_1_8197 26 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 252 3 8 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 252 (Polychromatic418967fa.accept_25_23_12_2_1_15224 23 87
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 252
  (Polychromatic418967fa.accept_17_5_2_14_1_4270 22 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 252 3 7 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 252 (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 87 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 252 3 6 29 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 252
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 252 3 5 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 87 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 252
  (Polychromatic418967fa.accept_19_13_11_5_1_5692 13 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 252 3 4 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 252 (Polychromatic418967fa.accept_19_10_11_5_1_7093 10 87
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 252 3 3 29 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 252
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 252 (Polychromatic418967fa.accept_22_7_21_10_1_15253 7 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 252 3 2 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 87 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 87 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 252 3 1 29 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 2 87 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 87 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 252
  (allA_succ_of_accept 85 86 252 (accept_3_4 85 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  252 2 42 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 252 (Polychromatic418967fa.accept_15_8_11_12_1_1626 83 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 252 2 41 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 81 86 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 252 2 40 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 252 (accept_3_4 79 86 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 252 2 39 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 252
  (Polychromatic418967fa.accept_13_12_8_5_1_976 77 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 252 2 38 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 75 86 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 252 2 37 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 252 (accept_3_4 73 86 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 252 2 36 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 71
  86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 252 2 35 43 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 252
  (Polychromatic418967fa.accept_22_3_20_10_1_12189 69 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 86 252 2 34 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 86 252 (accept_3_4 67 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 252 2 33 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 252 (Polychromatic418967fa.accept_19_8_10_5_1_9903 65 86 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 252 2 32 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 252
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 252 2 31 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 252 (accept_3_4 61 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 252 2 30 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 252 (Polychromatic418967fa.accept_15_14_11_12_1_4440 59 86 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 252 2 29 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 252
  (Polychromatic418967fa.accept_20_17_6_12_1_8185 57 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 252 2 28 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 252 (accept_3_4 55 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 252 2 27 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 53 86 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 252 2 26 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 252 2 25 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 252 (accept_3_4 49 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 252 2 24 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 252 (Polychromatic418967fa.accept_17_13_1_14_1_1149 47 86 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 252 2 23 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 252 2 22 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 252 (accept_3_4 43 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 252 2 21 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 86 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 252 2 20 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 252
  (Polychromatic418967fa.accept_22_17_20_10_1_12161 39 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 86 252 2 19 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 86 252 (accept_3_4 37 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 252 2 18 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 252 (Polychromatic418967fa.accept_19_16_10_5_1_7106 35 86 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 252 2 17 43 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 252
  (Polychromatic418967fa.accept_19_14_10_5_1_3073 33 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 252 2 16 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 252 (accept_3_4 31 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 252 2 15 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 29 86 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 252 2 14 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 252
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 252 2 13 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 252 (accept_3_4 25 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 252 2 12 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 86 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 252 2 11 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 252 2 10 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 252 (accept_3_4 19 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 252 2 9 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 252 (Polychromatic418967fa.accept_20_17_6_12_1_8185 17 86 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 252 2 8 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 252 (Polychromatic418967fa.accept_19_15_10_5_1_5637
  15 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 252 2 7 43 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 252 (accept_3_4 13
  86 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 252 2 6 43 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 252 2 5 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 252 (Polychromatic418967fa.accept_25_9_11_2_1_15252 9 86 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 252 2 4 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 252 (accept_3_4 7 86 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 252 2 3 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 252 (Polychromatic418967fa.accept_20_5_6_12_1_2444 5 86 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 252 2 2 43 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 3
  86 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 252 2 1 43 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 252 (accept_3_4 1 86
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 252
  (allA_succ_of_accept 84 85 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 84 85 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 252 (accept_3_5 83 85 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 82 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 81 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 85 252 (accept_3_5 80 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  85 252 (Polychromatic418967fa.accept_22_13_19_10_1_15251 79 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 85 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 252 (accept_3_5 77 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 85 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 76 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 252
  (Polychromatic418967fa.accept_11_9_8_10_1_934 75 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 85 252 (accept_3_5 74 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  85 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 85 252 (Polychromatic418967fa.accept_16_8_5_12_1_3812 72 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 252 (accept_3_5 71 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 85 252 (Polychromatic418967fa.accept_19_13_9_5_1_8541 70 85
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 69 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 85 252 (accept_3_5 68 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  85 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 67 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 85 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 66 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 252 (accept_3_5 65 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 85 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 64 85 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 63 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 252 (accept_3_5 62 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 252 (Polychromatic418967fa.accept_19_4_9_5_1_8572 61 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 85 252 (Polychromatic418967fa.accept_27_6_4_9_1_15250 60 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 252 (accept_3_5 59 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 58 85 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 57 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 252 (accept_3_5 56 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 252 (Polychromatic418967fa.accept_16_7_5_12_1_4824 55 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 252 (accept_3_5 53 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 252
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 51 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 252 (accept_3_5 50 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 252 (accept_3_5 47 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 252 (Polychromatic418967fa.accept_20_6_5_12_1_8169 46 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 252
  (Polychromatic418967fa.accept_19_7_9_5_1_8590 45 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 252 (accept_3_5 44 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 252 (accept_3_5 41 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 252 (Polychromatic418967fa.accept_16_8_5_12_1_3812 40 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 252 (accept_3_5 38 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 252 (accept_3_5 35 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 252 (Polychromatic418967fa.accept_19_15_9_5_1_5656 34 85
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 252 (accept_3_5 32 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 252 (Polychromatic418967fa.accept_20_10_5_12_1_13866 30 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 252 (accept_3_5 29 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 85 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 27 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 252 (accept_3_5 26 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 252 (accept_3_5 23 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 85
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 252
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 252 (accept_3_5 20 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 252 (Polychromatic418967fa.accept_25_19_10_2_1_15220 19 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 252 (accept_3_5 17 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 252 (Polychromatic418967fa.accept_24_16_13_12_1_8475 16 85 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 252
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 252 (accept_3_5 14 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 252 (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 252 (accept_3_5 11 85 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 252 (Polychromatic418967fa.accept_16_10_5_12_1_4925 10 85
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 252 (accept_3_5 8 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  252 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 85 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 252 (accept_3_5 5 85 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 252 (Polychromatic418967fa.accept_16_4_5_12_1_2749 4 85 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3
  85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 252 (accept_3_5 2 85 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1
  85 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 252
  (allA_succ_of_accept 83 84 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 83 84 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84 252 2 41 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 84 252 3 27 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 84 252 4 20 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610
  79 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 252 6 13 14 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 84 252 7 11 12 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 84 252 4 19 21 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 84 252 3 25 28 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 84 252 2 37 42 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 84 252
  (Polychromatic418967fa.accept_16_9_4_12_1_4896 73 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 252 12 6 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 71 84 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 252 14 5 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 84 252 3 23 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 84 252 4 17 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 67 84 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 252 6 11 14 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 65 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 252 4 16 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 84 252 21 3 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 84 252 2 31 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 84 252 (Polychromatic418967fa.accept_16_13_4_12_1_1805 61 84 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 252 12 5 7 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 252
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 84 252 2 29 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 84 252 3 19 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 84 252 28 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 84 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 55 84 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 252 6 9 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610
  53 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 252 4 13 21 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 84 252 3 17 28 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 84 252 2 25 42 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 84 252 7 7 12 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 84 252 12 4 7 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 252 2 23 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 84 252 3 15 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 84 252 4 11 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 84 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 43 84 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 252 42 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 252 (Polychromatic418967fa.accept_16_9_4_12_1_4896
  41 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 252 4 10 21 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 84 252 3 13 28 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 84 252 2 19 42 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 252 12 3 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 84 252 7 5 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 84 252 2 17 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 84 252 3 11 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 84 252 4 8 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 84 252 (Polychromatic418967fa.accept_16_15_4_12_1_2731 31 84 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 252 6 5 14 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 252
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 252 28 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 84 252 3 9 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 84 252 2 13 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 84 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 84 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 252 12 2 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297
  23 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 252 2 11 42 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 252 21 1 4 12
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 252 4 5 21 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 252
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 252 6 3 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 84 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 252 4 4 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 84 252 3 5 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 252 14 1 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 252 (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 84
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 252 12 1 7 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 252
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 84 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 252 2 5 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 84 252 3 3 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 84 252 4 2 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 84 252 7 1 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 84 252 6 1 14 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 84 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 252 4 1 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 84 252 3 1 28 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 84 252 2 1 42 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 1 84 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 252
  (allA_succ_of_accept 82 83 252 (accept_3_4 82 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 81 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 252 (Polychromatic418967fa.accept_15_5_8_12_1_2435 80 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 252 (accept_3_4 79 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 78 83 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 252
  (Polychromatic418967fa.accept_23_8_14_22_1_12013 77 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 83 252 (accept_3_4 76 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 83 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 75 83 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 83 252 (Polychromatic418967fa.accept_16_10_3_12_1_1758 74 83
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 252 (accept_3_4 73 83 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 252 (Polychromatic418967fa.accept_16_8_3_12_1_1819
  72 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 252 (accept_3_4 70 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 252 (Polychromatic418967fa.accept_19_12_7_5_1_5725 69 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 68 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 252 (accept_3_4 67 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 252 (Polychromatic418967fa.accept_19_9_7_5_1_9887 66 83 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 65 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 252 (accept_3_4 64 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 252 (Polychromatic418967fa.accept_22_18_17_10_1_12201 62 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 252 (accept_3_4 61 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 83
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 252
  (Polychromatic418967fa.accept_19_2_7_5_1_3067 59 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 252 (accept_3_4 58 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 252 (Polychromatic418967fa.accept_16_9_3_12_1_1802 57 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 252 (Polychromatic418967fa.accept_15_11_8_12_1_4437 56 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 252 (accept_3_4 55 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 252 (Polychromatic418967fa.accept_17_3_15_14_1_4219 54 83
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 252
  (Polychromatic418967fa.accept_20_13_3_12_1_15194 53 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 83 252 (accept_3_4 52 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 83 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 83 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 252 (Polychromatic418967fa.accept_15_5_8_12_1_2435 50 83
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 252 (accept_3_4 49 83 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 252 (Polychromatic418967fa.accept_15_3_8_12_1_900
  48 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 252 (accept_3_4 46 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 252 (Polychromatic418967fa.accept_19_6_7_5_1_256 44 83 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 252 (accept_3_4 43 83 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 252 (Polychromatic418967fa.accept_16_10_3_12_1_1758 42 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 41 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 252 (accept_3_4 40 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 252 (accept_3_4 37 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 36 83
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 252 (accept_3_4 34 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 252 (Polychromatic418967fa.accept_19_13_7_5_1_5712 32 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 252 (accept_3_4 31 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 252 (Polychromatic418967fa.accept_20_10_3_12_1_15195 30 83
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 252
  (Polychromatic418967fa.accept_17_12_15_14_1_6746 29 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 83 252 (accept_3_4 28 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 83 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 83 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 252 (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 83
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 252 (accept_3_4 25 83 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 252 (Polychromatic418967fa.accept_16_8_3_12_1_1819
  24 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 252 (accept_3_4 22 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 252 (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 252 (accept_3_4 19 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 83 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 252
  (Polychromatic418967fa.accept_19_17_7_5_1_1883 17 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 252 (accept_3_4 16 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 252 (Polychromatic418967fa.accept_31_14_21_4_1_15249 14 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 252 (accept_3_4 13 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 252 (Polychromatic418967fa.accept_17_12_15_14_1_6746 12 83
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 252 (accept_3_4 10 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 252 (Polychromatic418967fa.accept_16_9_3_12_1_1802 9 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 252 (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 83 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 252 (accept_3_4 7 83 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 252 (Polychromatic418967fa.accept_17_6_15_14_1_8027 6 83 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 252 (accept_3_4 4 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  252 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 83 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 252 (Polychromatic418967fa.accept_19_2_7_5_1_3067 2 83 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 252 (accept_3_4 1 83 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 252
  (allA_succ_of_accept 81 82 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 81 82 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 82 252 2 40 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 82 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 79
  82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 252 2 39 41 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 252 (accept_3_5 77
  82 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 252 2 38 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 75 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 82 252 2 37 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 82 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800 73 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 82 252 2 36 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 82 252 (accept_3_5 71 82 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82 252 2 35 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 82 252 (Polychromatic418967fa.accept_20_9_2_12_1_5144
  69 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 82 252 2 34 41 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 82 252
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 67 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 82 252 2 33 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 82 252 (accept_3_5 65 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 82 252 2 32 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 82 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 63 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 252 2 31 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 61 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 252 2 30 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 252 (accept_3_5 59 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 82 252 2 29 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 82 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800 57 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 252 2 28 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 252
  (Polychromatic418967fa.accept_15_10_7_12_1_2490 55 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 252 2 27 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 252 (accept_3_5 53 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 82 252 2 26 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 82 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 51 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 252 2 25 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 49 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 252 2 24 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 82 252 (accept_3_5 47 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 252 2 23 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 82 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 252 2 22 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 252
  (Polychromatic418967fa.accept_25_18_7_2_1_15248 43 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 252 2 21 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 82 252 (accept_3_5 41 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 252 2 20 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 82 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 252 2 19 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 37 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 252 2 18 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 82 252 (accept_3_5 35 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 82 252 2 17 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 252 2 16 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 252
  (Polychromatic418967fa.accept_16_15_2_12_1_1799 31 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 252 2 15 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 82 252 (accept_3_5 29 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 82 252 2 14 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 82 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 252 2 13 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 252
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 252 2 12 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 82 252 (accept_3_5 23 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 82 252 2 11 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 21 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 252 2 10 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 252 2 9 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 252 (accept_3_5 17 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  252 2 8 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 252 2 7 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 82 252 (Polychromatic418967fa.accept_25_13_7_2_1_15247 13 82 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 252 2 6 41 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 252 (accept_3_5 11 82 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 252 2 5 41 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 252
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 252 2 4 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 252 (Polychromatic418967fa.accept_16_7_2_12_1_1754 7 82 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 252 2 3 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 252 (accept_3_5 5 82 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 252 2 2 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 82 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 252 2 1 41 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 1
  82 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 252
  (allA_succ_of_accept 80 81 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 80 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 79 81 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 252 3 26 27 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 77 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 76 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 252 3 25 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605
  74 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 73 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 252 9 8 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 71 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 252 (Polychromatic418967fa.accept_15_10_6_12_1_1645 70 81
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 252 3 23 27 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 252
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 68 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 67 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 252 3 22 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 252 (Polychromatic418967fa.accept_15_5_6_12_1_916
  65 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 252
  (Polychromatic418967fa.accept_29_6_23_20_1_15246 64 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 81 252 9 7 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 81 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 62 81 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 61
  81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 252 3 20 27 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 59 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 252 (Polychromatic418967fa.accept_13_6_3_5_1_3167 58 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 252 3 19 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 56
  81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 252
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 55 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 252 9 6 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 252 (Polychromatic418967fa.accept_15_7_6_12_1_1614 52 81
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 252 3 17 27 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 252
  (Polychromatic418967fa.accept_13_11_3_5_1_982 50 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 252 3 16 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636
  47 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 46 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 252 9 5 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 252 (Polychromatic418967fa.accept_17_10_13_14_1_3094 44 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 81 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 252 3 14 27 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 252
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 41 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 40 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 252 3 13 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 252 (Polychromatic418967fa.accept_11_5_4_10_1_524
  38 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 37 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 252 9 4 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 34 81 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 252 3 11 27 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 252
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 32 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 252 (Polychromatic418967fa.accept_20_11_1_12_1_3803 31 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 252 3 10 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 29
  81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 252
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 252 9 3 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 252 (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 81
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 252 3 8 27 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 22 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 252 3 7 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 81 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 19 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 252 9 2 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 81 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 252 3 5 27 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 252 3 4 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 81 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 252
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 252 9 1 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 252 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 81 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 252 3 2 27 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 252 (Polychromatic418967fa.accept_16_4_1_12_1_1792 4 81 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 252 3 1 27 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 81 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 1 81 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 252
  (allA_succ_of_accept 79 80 252 (accept_3_4 79 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  252 2 39 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  77 80 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 77 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 252 4 19 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 75 80 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 252 2 37 40 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 252 (accept_3_4 73 80 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 252 4 18 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 252
  (Polychromatic418967fa.accept_23_2_11_22_1_15175 71 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 80 252 2 35 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 80 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 69 80 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 252 4 17 20 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 252 (accept_3_4 67 80 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 252 2 33 40 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 252
  (Polychromatic418967fa.accept_19_8_4_5_1_8569 65 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 80 252 4 16 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 80 252 (Polychromatic418967fa.accept_19_6_4_5_1_5650 63 80 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 252 2 31 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 252 (accept_3_4 61 80 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 252 4 15 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 252 (Polychromatic418967fa.accept_13_7_2_5_1_2344 59 80 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 252 2 29 40 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 252
  (Polychromatic418967fa.accept_25_7_5_2_1_11801 57 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 252 4 14 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 252 (accept_3_4 55 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  252 2 27 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 80 252 (Polychromatic418967fa.accept_15_8_5_12_1_4453 53 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 252 4 13 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 80 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 252 2 25 40 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 252 (accept_3_4 49 80 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 252 4 12 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 252
  (Polychromatic418967fa.accept_15_2_5_12_1_369 47 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 80 252 2 23 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 80 252 (Polychromatic418967fa.accept_17_11_12_14_1_5431 45 80 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 80 252 4 11 20 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 252 (accept_3_4 43 80 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 252 2 21 40 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 252
  (Polychromatic418967fa.accept_24_17_8_12_1_8499 41 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 252 4 10 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 80 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 252 2 19 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 252 (accept_3_4 37 80 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 252 4 9 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 80 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 80 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 252 2 17 40 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 252
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 252 4 8 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 252 (accept_3_4 31 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  252 2 15 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 80 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 252 4 7 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 252 (Polychromatic418967fa.accept_19_8_4_5_1_8569 27 80 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 252 2 13 40 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 252 (accept_3_4 25 80 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 252 4 6 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 80 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 252 2 11 40 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 252
  (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 252 4 5 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 252 (accept_3_4 19 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  252 2 9 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 252 4 4 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 252 (Polychromatic418967fa.accept_17_15_12_14_1_2087 15 80 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 252 2 7 40 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 252 (accept_3_4 13 80 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 252 4 3 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 252
  (Polychromatic418967fa.accept_17_11_12_14_1_5431 11 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 252 2 5 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 80 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 80 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 252 4 2 20 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 252 (accept_3_4 7 80 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 252 2 3 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80 252 (Polychromatic418967fa.accept_24_5_8_12_1_15245 5 80 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 252 4 1 20 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 252
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 252 2 1 40 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 252 (accept_3_4 1 80 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 252
  (allA_succ_of_accept 78 79 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 78 79 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 252 (accept_3_5 77 79 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 76 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 75 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 79 252 (accept_3_5 74 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  79 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176 73 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 79 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 72 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 252 (accept_3_5 71 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 79 252 (Polychromatic418967fa.accept_25_20_4_2_1_8207 70 79
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 252
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 69 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 79 252 (accept_3_5 68 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  79 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 79 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744 66 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 252 (accept_3_5 65 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 252 (Polychromatic418967fa.accept_13_12_1_5_1_1650 64 79
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 252
  (Polychromatic418967fa.accept_17_12_11_14_1_3120 63 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 79 252 (accept_3_5 62 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 79 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 61 79 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176 60 79 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 252 (accept_3_5 59 79 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 252 (Polychromatic418967fa.accept_13_6_1_5_1_3988
  58 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 252 (accept_3_5 56 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 55 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 54 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 252 (accept_3_5 53 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 252 (Polychromatic418967fa.accept_15_7_4_12_1_2530 52 79
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 252 (accept_3_5 50 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 252 (Polychromatic418967fa.accept_20_9_19_12_1_5221 49 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 48 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 252 (accept_3_5 47 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 46 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 252 (accept_3_5 44 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 252 (accept_3_5 41 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 40 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 252
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 252 (accept_3_5 38 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 252 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 252 (accept_3_5 35 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 79
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 252
  (Polychromatic418967fa.accept_17_16_11_14_1_4213 33 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 79 252 (accept_3_5 32 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 79 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 79 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 79 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 252 (accept_3_5 29 79 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 252
  (Polychromatic418967fa.accept_23_5_10_22_1_15244 28 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 252 (accept_3_5 26 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 252 (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 252
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 24 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 252 (accept_3_5 23 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 22 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 252 (accept_3_5 20 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 252
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 252 (accept_3_5 17 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 252 (Polychromatic418967fa.accept_25_15_4_2_1_15243 15 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 252 (accept_3_5 14 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 252 (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 79
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 252 (accept_3_5 11 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 252 (Polychromatic418967fa.accept_19_10_3_5_1_11346 10 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 252 (accept_3_5 8 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 6 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 252 (accept_3_5 5 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 79 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 252 (accept_3_5 2 79 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 79 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 252
  (allA_succ_of_accept 77 78 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 77 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 252 2 38 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 78 252 3 25 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 78 252 2 37 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 73 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 78 252 6 12 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 78 252 (Polychromatic418967fa.accept_19_14_2_5_1_9949 71 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 252 2 35 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 78 252 3 23 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 78 252 2 34 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 67 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 78 252 6 11 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 78 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 252 2 32 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 78 252 3 21 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 78 252 2 31 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 252
  (Polychromatic418967fa.accept_19_4_2_5_1_5677 61 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 252 6 10 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 252 (Polychromatic418967fa.accept_22_15_12_10_1_10700 59 78 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 252 2 29 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 78 252 3 19 26 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 78 252 2 28 39 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 55 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 252 6 9 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 78 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 53 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 252 2 26 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 78 252 3 17 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 78 252 2 25 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 252
  (Polychromatic418967fa.accept_24_1_6_12_1_8449 49 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 252 6 8 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 47 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 252 2 23 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 78 252 3 15 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 78 252 2 22 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 252 6 7 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 252 (Polychromatic418967fa.accept_17_7_10_14_1_8022 41 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 252 2 20 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 252 3 13 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 252 2 19 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 37 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 252 6 6 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 78 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 252 2 17 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 252 3 11 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 78 252 2 16 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 31 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 252 6 5 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 252 (Polychromatic418967fa.accept_19_10_2_5_1_3059 29 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 252 2 14 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 78 252 3 9 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 252 2 13 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 252 6 4 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 252 2 11 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 78 252 3 7 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 78 252 2 10 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 252
  (Polychromatic418967fa.accept_23_19_9_22_1_15210 19 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 78 252 6 3 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 78 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 78 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 252 2 8 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 252 3 5 26 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 252 2 7 39 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 13 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 252 6 2 13 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 252 (Polychromatic418967fa.accept_22_11_12_10_1_1424 11 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 252 2 5 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 78 252 3 3 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 78 252 2 4 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 7
  78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 252 6 1 13 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 78 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 78 252 2 2 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 78 252 3 1 26 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 78 252 2 1 39 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 252 (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 78 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 252
  (allA_succ_of_accept 76 77 252 (accept_3_4 76 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 75 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 252 (accept_3_4 73 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603 72 77 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 71 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 77 252 7 10 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 69 77 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 252 (Polychromatic418967fa.accept_16_4_13_12_1_1740 68 77
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 252 (accept_3_4 67 77 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601
  66 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 252 (accept_3_4 64 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 77
  252 7 9 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  77 252 (Polychromatic418967fa.accept_20_2_17_12_1_5178 62 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 77 252 (accept_3_4 61 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 77 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 60 77 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 59 77 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 252 (accept_3_4 58 77 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 57
  77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 252 7 8 11 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 77 252 (accept_3_4 55
  77 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 54 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 53 77 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 252 (accept_3_4 52 77 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 51 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543
  50 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 77 252 7 7 11 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 77 252
  (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 77 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 47 77 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 252 (accept_3_4 46 77 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 77 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 252 (Polychromatic418967fa.accept_10_4_7_2_1_211
  44 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 252 (accept_3_4 43
  77 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77 252 7 6 11 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 77 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 252 (accept_3_4 40 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 252 (Polychromatic418967fa.accept_17_4_9_14_1_5406 38 77 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 252 (accept_3_4 37 77 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 77 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 77 252 7 5 11 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 77 252 (accept_3_4 34 77 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 33
  77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 252 (accept_3_4 31 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 77 252 7 4 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 77 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601
  27 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 252
  (Polychromatic418967fa.accept_16_10_13_12_1_4873 26 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 77 252 (accept_3_4 25 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 77 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 77 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 252 (Polychromatic418967fa.accept_19_4_1_5_1_9933 23 77 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 252 (accept_3_4 22 77 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77 252 7 3 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 77 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603
  20 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 252 (accept_3_4 19
  77 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 252
  (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 77 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 252 (accept_3_4 16 77 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 77 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 77 252 7 2 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 77 252 (accept_3_4 13 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 252 (Polychromatic418967fa.accept_17_12_9_14_1_4283 12 77 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 252
  (Polychromatic418967fa.accept_23_11_8_22_1_8821 11 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 252 (accept_3_4 10 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 77 252 7 1 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 77 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6
  77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 252 (accept_3_4 4 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 77 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 77 252 (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 252 (accept_3_4 1 77 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 77 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 76 252 (allA_succ_of_accept 75 76 252 (Polychromatic418967fa.accept_17_7_8_14_1_6720 75 76 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 76 252 2 37 38 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 76 252
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 73 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 76 252 4 18 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 76 252 (accept_3_5 71 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76
  252 2 35 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  69 76 252 (Polychromatic418967fa.accept_27_15_22_9_1_15242 69 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 76 252 4 17 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 76 252 (Polychromatic418967fa.accept_17_16_8_14_1_6757 67 76 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 76 252 2 33 38 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 76 252 (accept_3_5 65 76 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76 252 4 16 19 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 76 252
  (Polychromatic418967fa.accept_26_11_24_18_1_15241 63 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 76 252 2 31 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 76 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 61 76 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 252 4 15 19 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 252 (accept_3_5 59 76 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 252 2 29 38 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 252
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 57 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 252 4 14 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 55 76 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 252 2 27 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 252 (accept_3_5 53 76 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 252 4 13 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 76 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 252 2 25 38 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 252
  (Polychromatic418967fa.accept_15_4_1_12_1_914 49 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 252 4 12 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 252 (accept_3_5 47 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  252 2 23 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 76 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 45 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 252 4 11 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 43 76 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 252 2 21 38 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 252 (accept_3_5 41 76 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 252 4 10 19 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 252
  (Polychromatic418967fa.accept_26_13_24_18_1_15240 39 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 76 252 2 19 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 76 252 (Polychromatic418967fa.accept_24_13_4_12_1_15239 37 76 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 252 4 9 19 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 252 (accept_3_5 35 76 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 252 2 17 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302
  33 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 252 4 8 19 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 252 2 15 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 76 252 (accept_3_5 29 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 76 252 4 7 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 76 252 (Polychromatic418967fa.accept_29_27_18_20_1_15238 27 76 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 252 2 13 38 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 252
  (Polychromatic418967fa.accept_24_1_4_12_1_10366 25 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 252 4 6 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 76 252 (accept_3_5 23 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76
  252 2 11 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 76 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 76 252 4 5 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 76 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 76 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 252 2 9 38 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 252 (accept_3_5 17 76 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 252 4 4 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 76 252 (Polychromatic418967fa.accept_23_15_7_22_1_12021 15 76
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 252 2 7 38 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 252
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 76 252 4 3 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 252 (accept_3_5 11 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76
  252 2 5 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  76 252 (Polychromatic418967fa.accept_25_9_1_2_1_15237 9 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 76 252 4 2 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 76 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 76 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 252 2 3 38 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 252 (accept_3_5 5 76 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 252 4 1 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 76 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 76 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 252 2 1 38 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 76 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 252
  (allA_succ_of_accept 74 75 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 74 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 73 75 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 252 3 24 25 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 252 (Polychromatic418967fa.accept_19_13_18_5_1_8619 70 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 252 3 23 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 68
  75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 67 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 252 3 22 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 252 (Polychromatic418967fa.accept_16_1_11_12_1_1774 65 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 252 (Polychromatic418967fa.accept_30_4_15_12_1_15236 64 75
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 252 3 21 25 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 252
  (Polychromatic418967fa.accept_22_18_9_10_1_1478 62 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 252 (Polychromatic418967fa.accept_17_10_7_14_1_4244 61 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 252 3 20 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 252 (Polychromatic418967fa.accept_17_8_7_14_1_11730
  59 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 58 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 252 3 19 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 56 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 75 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 252 3 18 25 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 53 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 52 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 252 3 17 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 252
  (Polychromatic418967fa.accept_20_10_15_12_1_11131 50 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 75 252 (Polychromatic418967fa.accept_16_1_11_12_1_1774 49 75 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 252 3 16 25 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 252 (Polychromatic418967fa.accept_20_6_15_12_1_6637 46 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 252 3 15 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 252 (Polychromatic418967fa.accept_17_10_7_14_1_4244
  44 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 43 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 75 252 3 14 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 252 (Polychromatic418967fa.accept_16_8_11_12_1_962 40 75
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 75 252 3 13 25 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 252 3 12 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 252
  (Polychromatic418967fa.accept_22_13_9_10_1_15235 35 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 75 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 34 75 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 252 3 11 25 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 32 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 252 3 10 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 252 (Polychromatic418967fa.accept_19_10_18_5_1_5673
  29 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 28 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 75 252 3 9 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 252 (Polychromatic418967fa.accept_16_10_11_12_1_4835 26 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 252 (Polychromatic418967fa.accept_17_8_7_14_1_11730 25 75
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 252 3 8 25 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 252 (Polychromatic418967fa.accept_26_22_23_18_1_15234 22 75 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 252 3 7 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 252 (Polychromatic418967fa.accept_16_4_11_12_1_1775
  20 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 252
  (Polychromatic418967fa.accept_11_8_9_10_1_503 19 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 252 3 6 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 252 (Polychromatic418967fa.accept_23_16_6_22_1_12036 16 75
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 252 3 5 25 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 252
  (Polychromatic418967fa.accept_27_14_21_9_1_3603 14 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 252 3 4 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 252 (Polychromatic418967fa.accept_27_11_21_9_1_15233 11 75
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 252
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 10 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 75 252 3 3 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 75 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 75 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7
  75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 252 3 2 25 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 252
  (Polychromatic418967fa.accept_20_5_15_12_1_9720 5 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 75 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 252 3 1 25 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 2 75 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 1 75 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 252
  (allA_succ_of_accept 73 74 252 (accept_3_4 73 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74
  252 2 36 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  71 74 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 71 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 74 252 2 35 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 74 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 69 74 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 252 2 34 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 252 (accept_3_4 67 74 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 252 2 33 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 252
  (Polychromatic418967fa.accept_27_11_20_9_1_11601 65 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 74 252 2 32 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 74 252 (Polychromatic418967fa.accept_22_19_8_10_1_12142 63 74 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 74 252 2 31 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 74 252 (accept_3_4 61 74 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74 252 2 30 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 74 252
  (Polychromatic418967fa.accept_16_11_10_12_1_4832 59 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 252 2 29 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 74 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 252 2 28 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 252 (accept_3_4 55 74 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 252 2 27 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 252
  (Polychromatic418967fa.accept_11_9_8_10_1_934 53 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 74 252 2 26 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 74 252 (Polychromatic418967fa.accept_16_3_10_12_1_4814 51 74 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 252 2 25 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 252 (accept_3_4 49 74 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 252 2 24 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 74 252 2 23 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 74 252 (Polychromatic418967fa.accept_16_13_10_12_1_1811 45 74 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 252 2 22 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 252 (accept_3_4 43 74 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 252 2 21 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 252
  (Polychromatic418967fa.accept_13_2_9_5_1_959 41 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 74 252 2 20 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 74 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 74 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 252 2 19 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 252 (accept_3_4 37 74 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 252 2 18 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 252 (Polychromatic418967fa.accept_16_3_10_12_1_4814
  35 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 252 2 17 37 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 252
  (Polychromatic418967fa.accept_19_14_17_5_1_15232 33 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 74 252 2 16 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 74 252 (accept_3_4 31 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 252 2 15 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 29 74 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 252 2 14 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 252 2 13 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 252 (accept_3_4 25 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 252 2 12 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 252 (Polychromatic418967fa.accept_26_23_22_18_1_15231 23 74 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 252 2 11 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 252
  (Polychromatic418967fa.accept_16_5_10_12_1_4904 21 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 252 2 10 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 252 (accept_3_4 19 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 252 2 9 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 74 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 252 2 8 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 15
  74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 252 2 7 37 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 252 (accept_3_4 13
  74 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 252 2 6 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 252
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 252 2 5 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 74 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 74 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 252 2 4 37 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 252 (accept_3_4 7 74 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 252 2 3 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74 252 (Polychromatic418967fa.accept_16_5_10_12_1_4904 5 74 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 252 2 2 37 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 252 2 1 37 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 252 (accept_3_4 1 74 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 252 (allA_succ_of_accept
  72 73 252 (Polychromatic418967fa.accept_16_8_9_12_1_1737 72 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 252 (accept_3_5 71 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 252 (Polychromatic418967fa.accept_15_10_13_12_1_3384 70 73 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 73 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 252 (accept_3_5 68 73 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 252 (Polychromatic418967fa.accept_16_3_9_12_1_4831
  67 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 252
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 66 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 252 (accept_3_5 65 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 64 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 63 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 252 (accept_3_5 62 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 73 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 252
  (Polychromatic418967fa.accept_17_9_5_14_1_4277 60 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 252 (accept_3_5 59 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 58 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 252 (Polychromatic418967fa.accept_25_7_23_2_1_15229 57 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 252 (accept_3_5 56 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 55 73 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 252
  (Polychromatic418967fa.accept_23_8_4_22_1_8781 54 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 252 (accept_3_5 53 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 252 (Polychromatic418967fa.accept_16_4_9_12_1_4829 52 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 252 (accept_3_5 50 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 48 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 252 (accept_3_5 47 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 252 (Polychromatic418967fa.accept_15_1_13_12_1_347 46 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 252 (accept_3_5 44 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 252 (Polychromatic418967fa.accept_17_9_5_14_1_4277 43 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 252
  (Polychromatic418967fa.accept_13_3_8_5_1_974 42 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 252 (accept_3_5 41 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 40 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 252 (Polychromatic418967fa.accept_19_1_16_5_1_5671 39 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 252 (accept_3_5 38 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 73 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 252
  (Polychromatic418967fa.accept_11_3_7_10_1_180 36 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 252 (accept_3_5 35 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 252 (Polychromatic418967fa.accept_16_2_9_12_1_46 34 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 33 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 252 (accept_3_5 32 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 73 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 252
  (Polychromatic418967fa.accept_19_11_16_5_1_5667 30 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 252 (accept_3_5 29 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 252 (Polychromatic418967fa.accept_23_5_4_22_1_15230 28 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 252 (accept_3_5 26 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 252
  (Polychromatic418967fa.accept_16_8_9_12_1_1737 24 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 252 (accept_3_5 23 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 252 (Polychromatic418967fa.accept_19_3_16_5_1_7098 22 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 252 (accept_3_5 20 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 252 (Polychromatic418967fa.accept_16_3_9_12_1_4831 19 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 18 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 252 (accept_3_5 17 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 16 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 252 (accept_3_5 14 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 252
  (Polychromatic418967fa.accept_13_12_8_5_1_976 12 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 252 (accept_3_5 11 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 252 (Polychromatic418967fa.accept_17_9_5_14_1_4277 9 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 252 (accept_3_5 8 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 252 (Polychromatic418967fa.accept_25_7_23_2_1_15229 7 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 252
  (Polychromatic418967fa.accept_24_6_1_12_1_10291 6 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 252 (accept_3_5 5 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  252 (Polychromatic418967fa.accept_16_4_9_12_1_4829 4 73 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 252 (accept_3_5 2 73 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 73 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 252 (allA_succ_of_accept 71
  72 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 71 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 72 252 2 35 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 72 252 3 23 24 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 72 252 4 17 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 72 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 67 72 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 252 6 11 12 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 252
  (Polychromatic418967fa.accept_16_1_8_12_1_405 65 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 252 4 16 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 72 252 9 7 8 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 72 252 2 31 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 72 252 (Polychromatic418967fa.accept_16_13_8_12_1_2723 61 72 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 252 12 5 6 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 252
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 59 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 72 252 2 29 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 72 252 3 19 24 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 72 252 4 14 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 72 252 (Polychromatic418967fa.accept_16_7_8_12_1_4902 55 72 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 252 18 3 4 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 252 (Polychromatic418967fa.accept_16_5_8_12_1_1766
  53 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 252 4 13 18 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 72 252 3 17 24 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 72 252 2 25 36 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 252 12 4 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 72 252 (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 72 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 252 2 23 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 72 252 9 5 8 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 72 252 4 11 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 252 (Polychromatic418967fa.accept_16_11_8_12_1_1767
  43 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 252 6 7 12 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 252
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 41 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 252 4 10 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 72 252 3 13 24 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 72 252 2 19 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 72 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 72 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 252 36 1 2 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 252 (Polychromatic418967fa.accept_16_3_8_12_1_2736
  35 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 252 2 17 36 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 252 3 11 24 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 252 4 8 18 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 252
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 31 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 252 6 5 12 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 252 (Polychromatic418967fa.accept_16_13_8_12_1_2723 29 72 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 252 4 7 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 72 252 9 3 8 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 72 252 2 13 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 252 (Polychromatic418967fa.accept_13_12_7_5_1_3147
  25 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 252 12 2 6 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 252
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 23 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 72 252 2 11 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 72 252 3 7 24 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 72 252 4 5 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 252 (Polychromatic418967fa.accept_16_3_8_12_1_2736 19 72 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 252 18 1 4 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 252 (Polychromatic418967fa.accept_16_1_8_12_1_405
  17 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 252 4 4 18 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 72 252 3 5 24 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 72 252 2 7 36 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 252
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 13 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 252 12 1 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 72 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 252 2 5 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 72 252 9 1 8 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 72 252 4 2 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 252 (Polychromatic418967fa.accept_16_7_8_12_1_4902 7
  72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 252 6 1 12 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 72 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 252 4 1 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 72 252 3 1 24 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 72 252 2 1 36 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 252 (Polychromatic418967fa.accept_16_1_8_12_1_405 1 72 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 252 (allA_succ_of_accept 70
  71 252 (accept_3_4 70 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 69 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 68 71 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 252 (accept_3_4 67 71 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 71 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 252 (Polychromatic418967fa.accept_19_8_14_5_1_9919
  65 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 252 (accept_3_4 64
  71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 63 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 71 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 62 71 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 252 (accept_3_4 61 71 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 71 252 (Polychromatic418967fa.accept_19_3_14_5_1_8597 60 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 252 (accept_3_4 58 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 252 (Polychromatic418967fa.accept_17_6_3_14_1_2078 57 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 71 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 252 (accept_3_4 55 71 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 252 (Polychromatic418967fa.accept_19_16_14_5_1_9920 54 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 53 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 252 (accept_3_4 52 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 50 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 252 (accept_3_4 49 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 48 71 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 252
  (Polychromatic418967fa.accept_19_9_14_5_1_1890 47 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 252 (accept_3_4 46 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 252 (Polychromatic418967fa.accept_17_11_3_14_1_6736 45 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 252 (Polychromatic418967fa.accept_15_14_11_12_1_4440 44 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 252 (accept_3_4 43 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 42 71 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 252
  (Polychromatic418967fa.accept_19_3_14_5_1_8597 41 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 252 (accept_3_4 40 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 38 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 252 (accept_3_4 37 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 71 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 252 (accept_3_4 34 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 252 (Polychromatic418967fa.accept_17_15_3_14_1_4230 32 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 252 (accept_3_4 31 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 30 71 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 29 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 252 (accept_3_4 28 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 71 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 252 (accept_3_4 25 71 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 252 (accept_3_4 22 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 252 (Polychromatic418967fa.accept_16_5_7_12_1_7206 21 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 252 (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 252 (accept_3_4 19 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 252 (Polychromatic418967fa.accept_16_2_7_12_1_3793 18 71
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 252 (accept_3_4 16 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 71 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 252 (accept_3_4 13 71 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 252 (accept_3_4 10 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 252 (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 71 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 252 (accept_3_4 7 71 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 71 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 252
  (Polychromatic418967fa.accept_16_5_7_12_1_7206 5 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 252 (accept_3_4 4 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 71 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 252 (Polychromatic418967fa.accept_16_2_7_12_1_3793 2 71 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 252 (accept_3_4 1 71 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 252
  (allA_succ_of_accept 69 70 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 69 70 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 70 252 2 34 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 70 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403
  67 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 252 2 33 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 252
  (accept_3_5 65 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 252 2 32 35 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 70 252 7 9 10 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 70 252 2 31 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 252
  (Polychromatic418967fa.accept_22_17_4_10_1_7339 61 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 252 2 30 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 70 252 (accept_3_5 59 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 70 252 2 29 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 70 252 (Polychromatic418967fa.accept_25_7_20_2_1_15228 57 70 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 252 14 4 5 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 252
  (Polychromatic418967fa.accept_20_15_10_12_1_13874 55 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 70 252 2 27 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 70 252 (accept_3_5 53 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 252 2 26 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 70 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 51 70 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 252 2 25 35 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 70 252 7 7 10 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 70 252 2 24 35 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 252 (accept_3_5 47
  70 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 252 2 23 35 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 252
  (Polychromatic418967fa.accept_19_7_13_5_1_7125 45 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 70 252 2 22 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 70 252 (Polychromatic418967fa.accept_15_13_10_12_1_2503 43 70 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 252 14 3 5 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 252 (accept_3_5 41 70 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 252 2 20 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625
  39 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 252 2 19 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 252
  (Polychromatic418967fa.accept_15_7_10_12_1_2403 37 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 70 252 2 18 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 70 252 7 5 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 70 252 2 17 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 70 252 (Polychromatic418967fa.accept_17_16_2_14_1_6715 33 70 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 252 2 16 35 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 252
  (Polychromatic418967fa.accept_19_12_13_5_1_11331 31 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 70 252 2 15 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 70 252 (accept_3_5 29 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 70 252 14 2 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 70 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 70 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 252 2 13 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 252 (Polychromatic418967fa.accept_20_5_10_12_1_8200
  25 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 252 2 12 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 252
  (accept_3_5 23 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 252 2 11 35 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 70 252 7 3 10 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 70 252 2 10 35 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 252
  (Polychromatic418967fa.accept_25_19_20_2_1_15227 19 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 70 252 2 9 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 70 252 (accept_3_5 17 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 70 252 2 8 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 70 252 (Polychromatic418967fa.accept_20_15_10_12_1_13874 15 70 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 252 14 1 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 252
  (Polychromatic418967fa.accept_15_13_10_12_1_2503 13 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 70 252 2 6 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 70 252 (accept_3_5 11 70 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 70 252 2 5 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 70 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 70 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 252 2 4 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 70 252 7 1 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 70 252 2 3 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 252 (accept_3_5 5 70 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 70 252 2 2 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 70 252 (Polychromatic418967fa.accept_17_3_2_14_1_6714 3 70 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 252 2 1 35 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 252 (Polychromatic418967fa.accept_25_1_20_2_1_9997 1
  70 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 252 (allA_succ_of_accept 68 69
  252 (Polychromatic418967fa.accept_16_4_5_12_1_2749 68 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 69 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 67 69 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 252 3 22 23 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 64 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 252 3 21 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  62 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 61 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 252 3 20 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498 59 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 58 69 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 252 3 19 23 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 252
  (Polychromatic418967fa.accept_16_8_5_12_1_3812 56 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 252 (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 252 3 18 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 53
  69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 252
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 52 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 252 3 17 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 50 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 69 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 252 3 16 23 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 252 (Polychromatic418967fa.accept_19_8_12_5_1_7122 46 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 252 3 15 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498
  44 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 252
  (Polychromatic418967fa.accept_20_3_9_12_1_6671 43 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 252 3 14 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 40 69
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 252 3 13 23 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 252
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 38 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 252 3 12 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651
  35 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 252
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 34 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 252 3 11 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 32 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 69 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 252 3 10 23 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 252 3 9 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 252 (Polychromatic418967fa.accept_16_10_5_12_1_4925 26 69
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 25 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 252 3 8 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 22 69 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 252 3 7 23 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 252 3 6 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 69 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 252
  (Polychromatic418967fa.accept_19_16_12_5_1_8578 16 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 252 3 5 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 14 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 252 (Polychromatic418967fa.accept_17_13_1_14_1_1149 13 69
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 252 3 4 23 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 252 3 3 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 252 (Polychromatic418967fa.accept_16_8_5_12_1_3812 8 69 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 252 3 2 23 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 69 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 252 3 1 23 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 252
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 69 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 69 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 252 (allA_succ_of_accept 67 68 252 (accept_3_4 67 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 68 252 2 33 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 68 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 68 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 68 252 4 16 17 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 68 252
  (Polychromatic418967fa.accept_13_11_3_5_1_982 63 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 68 252 2 31 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 68 252 (accept_3_4 61 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 68 252 4 15 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 68 252 (Polychromatic418967fa.accept_16_11_4_12_1_1760 59 68 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 252 2 29 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 252 (Polychromatic418967fa.accept_16_9_4_12_1_4896
  57 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 252 4 14 17 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 252 (accept_3_4 55
  68 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 252 2 27 34 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 53 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 68 252 4 13 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 68 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 51 68 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 252 2 25 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 252 (accept_3_4 49 68 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 252 4 12 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 47 68 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 252 2 23 34 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 252 4 11 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 68 252 (accept_3_4 43 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68
  252 2 21 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 68 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 41 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 68 252 4 10 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 68 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 68 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 252 2 19 34 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 252 (accept_3_4 37 68 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 252 4 9 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 35
  68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 252 2 17 34 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 252
  (Polychromatic418967fa.accept_15_3_8_12_1_900 33 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 252 4 8 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 252 (accept_3_4 31 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  252 2 15 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 68 252 (Polychromatic418967fa.accept_16_13_4_12_1_1805 29 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 252 4 7 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 68 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 252 2 13 34 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 252 (accept_3_4 25 68 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 252 4 6 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 68 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 252 2 11 34 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 252
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 252 4 5 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 252 (accept_3_4 19 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  252 2 9 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 252 (Polychromatic418967fa.accept_16_1_4_12_1_376 17 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 252 4 4 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 68 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 252 2 7 34 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 252 (accept_3_4 13 68 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 252 4 3 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 68 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 252 2 5 34 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 252
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 252 4 2 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 252 (accept_3_4 7 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 252
  2 3 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 252 4 1 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 68 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 252 2 1 34 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 252 (accept_3_4 1 68 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 252
  (allA_succ_of_accept 66 67 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 66 67 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 67 252 (accept_3_5 65 67 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 67 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 63
  67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 252 (accept_3_5 62 67
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 252
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 61 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 67 252 (Polychromatic418967fa.accept_19_3_10_5_1_4314 60 67 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 67 252 (accept_3_5 59 67 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 67 252 (Polychromatic418967fa.accept_16_10_3_12_1_1758 58 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 67 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 57 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 67 252 (accept_3_5 56 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  67 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 67 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 67 252 (accept_3_5 53 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 67 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 52 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 67 252
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 51 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 67 252 (accept_3_5 50 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  67 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 67 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 48 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 252 (accept_3_5 47 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 67 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 46 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 45 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 67 252 (accept_3_5 44 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  67 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 43 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 67 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 252 (accept_3_5 41 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 67 252 (Polychromatic418967fa.accept_15_10_7_12_1_2490 40 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 252 (accept_3_5 38 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 252 (Polychromatic418967fa.accept_19_18_10_5_1_12639 37 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 252 (accept_3_5 35 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 67 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 252
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 252 (accept_3_5 32 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 252 (accept_3_5 29 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 252 (Polychromatic418967fa.accept_17_11_16_14_1_6760 28 67 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 252
  (Polychromatic418967fa.accept_19_8_10_5_1_9903 27 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 252 (accept_3_5 26 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 252 (accept_3_5 23 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 22 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 252
  (Polychromatic418967fa.accept_15_6_7_12_1_869 21 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 252 (accept_3_5 20 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 18 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 252 (accept_3_5 17 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 252 (accept_3_5 14 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 252 (accept_3_5 11 67 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 67
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 9 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 252 (accept_3_5 8 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 67 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 6 67 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 252 (accept_3_5 5 67 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 67 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 3
  67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 252 (accept_3_5 2 67 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 252
  (Polychromatic418967fa.accept_23_1_21_22_1_15226 1 67 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 67 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 252
  (allA_succ_of_accept 65 66 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 65 66 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 252 2 32 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 66 252 3 21 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 66 252 2 31 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 61 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 252 6 10 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 252 (Polychromatic418967fa.accept_24_11_18_12_1_10165 59 66 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 252 2 29 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 66 252 3 19 22 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 66 252 2 28 33 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 252
  (Polychromatic418967fa.accept_13_3_1_5_1_499 55 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 252 6 9 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 252 (Polychromatic418967fa.accept_19_15_9_5_1_5656 53 66 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 252 2 26 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 66 252 3 17 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 66 252 2 25 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 252
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 49 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 252 6 8 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 66 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176 47 66 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 252 2 23 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 66 252 3 15 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 66 252 2 22 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 252
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 43 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 252 6 7 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 66 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 252 2 20 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 66 252 3 13 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 66 252 2 19 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 252 6 6 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 35 66 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 252 2 17 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 252 3 11 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 252 2 16 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 252 6 5 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 29 66 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 252 2 14 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 66 252 3 9 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 66 252 2 13 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 252 6 4 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 252 (Polychromatic418967fa.accept_16_7_2_12_1_1754 23 66 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 252 2 11 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 252 3 7 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 66 252 2 10 33 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 252 6 3 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 66 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 252 2 8 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 252 3 5 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 252 2 7 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 252 (Polychromatic418967fa.accept_19_13_9_5_1_8541
  13 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 252 6 2 11 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 252 2 5 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 66 252 3 3 22 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 66 252 2 4 33 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 252 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 66 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 252 6 1 11 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 66 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 252 2 2 33 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 66 252 3 1 22 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 66 252 2 1 33 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 66 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 252
  (allA_succ_of_accept 64 65 252 (accept_3_4 64 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 252 (Polychromatic418967fa.accept_15_2_5_12_1_369 62 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 252 (accept_3_4 61 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 252 (Polychromatic418967fa.accept_19_3_8_5_1_1875 60 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 252
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 59 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 252 (accept_3_4 58 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 252 (Polychromatic418967fa.accept_16_8_1_12_1_984 56 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 252 (accept_3_4 55 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 54 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 53 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 252 (accept_3_4 52 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 252 (Polychromatic418967fa.accept_16_2_1_12_1_3798 50 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 252 (accept_3_4 49 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 65 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 47 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 252 (accept_3_4 46 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 252 (Polychromatic418967fa.accept_24_20_17_12_1_10268 44 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 252 (accept_3_4 43 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 252 (Polychromatic418967fa.accept_19_4_8_5_1_5636 42 65 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 252
  (Polychromatic418967fa.accept_19_3_8_5_1_1875 41 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 252 (accept_3_4 40 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 252 (accept_3_4 37 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 252
  (Polychromatic418967fa.accept_19_16_8_5_1_4322 35 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 252 (accept_3_4 34 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 252 (Polychromatic418967fa.accept_15_2_5_12_1_369 32 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 252 (accept_3_4 31 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 252 (Polychromatic418967fa.accept_20_10_5_12_1_13866 30 65 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 252 (accept_3_4 28 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 252 (Polychromatic418967fa.accept_20_6_5_12_1_8169 26 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 252 (accept_3_4 25 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 24 65
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 252 (accept_3_4 22 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 252 (Polychromatic418967fa.accept_16_4_1_12_1_1792 20 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 252 (accept_3_4 19 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 65 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 252
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 252 (accept_3_4 16 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 252 (Polychromatic418967fa.accept_20_15_5_12_1_15225 15 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 252 (Polychromatic418967fa.accept_19_14_8_5_1_8606 14 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 252 (accept_3_4 13 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 252 (Polychromatic418967fa.accept_19_12_8_5_1_8538 12 65
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 252
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 252 (accept_3_4 10 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 252 (accept_3_4 7 65 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 65 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 252 (accept_3_4 4 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 65 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 252 (Polychromatic418967fa.accept_15_2_5_12_1_369 2 65 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 252 (accept_3_4 1 65 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 252
  (allA_succ_of_accept 63 64 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 63 64 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 252 2 31 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401
  61 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 252 4 15 16 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 252 (accept_3_5 59
  64 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 252 2 29 32 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 252 4 14 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 252 (Polychromatic418967fa.accept_17_4_13_14_1_1139 55 64 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 252 2 27 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 252 (accept_3_5 53 64 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 252 4 13 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 252 (Polychromatic418967fa.accept_19_13_7_5_1_5712 51 64 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 252 2 25 32 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 252
  (Polychromatic418967fa.accept_23_3_18_22_1_13682 49 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 64 252 4 12 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 64 252 (accept_3_5 47 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 64 252 2 23 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 64 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 64 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 64 252 4 11 16 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 64 252
  (Polychromatic418967fa.accept_13_4_12_5_1_476 43 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 64 252 2 21 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 64 252 (accept_3_5 41 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 64 252 4 10 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 64 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 64 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 252 2 19 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 37
  64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 252 4 9 16 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 252 (accept_3_5 35
  64 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 252 2 17 32 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 252
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 33 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 64 252 4 8 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 64 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 31 64 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 252 2 15 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 252 (accept_3_5 29 64 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 252 4 7 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 64 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 64 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 252 2 13 32 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 252
  (Polychromatic418967fa.accept_19_6_7_5_1_256 25 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 252 4 6 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 252 (accept_3_5 23 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  252 2 11 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 64 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 252 4 5 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 64 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 252 2 9 32 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 252 (accept_3_5 17 64 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 252 4 4 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 64 252 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 64 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 252 2 7 32 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 252
  (Polychromatic418967fa.accept_19_13_7_5_1_5712 13 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 252 4 3 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 252 (accept_3_5 11 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  252 2 5 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 252 4 2 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 64 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 252 2 3 32 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 252 (accept_3_5 5 64 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 252 4 1 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 252 (Polychromatic418967fa.accept_19_3_7_5_1_12632 3 64 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 252 2 1 32 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 1 64 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 252
  (allA_succ_of_accept 62 63 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 62 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 61 63 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 252 3 20 21 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 63 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 58 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 252 3 19 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 63 252 7 8 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 55
  63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 252 9 6 7 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 252
  (Polychromatic418967fa.accept_11_9_8_10_1_934 53 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 52 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 252 3 17 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744
  50 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 252 7 7 9 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 63 252 3 16 21 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 252
  (Polychromatic418967fa.accept_15_2_3_12_1_891 47 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 46 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 252 9 5 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 252 (Polychromatic418967fa.accept_23_21_17_22_1_13723 44 63
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 252 21 2 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 41 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 40 63
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 252 3 13 21 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 252
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 38 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 252 9 4 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 63 252 7 5 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744 34 63
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 252 3 11 21 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 252
  (Polychromatic418967fa.accept_13_6_11_5_1_133 32 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 252 3 10 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348
  29 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 252 7 4 9 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 63 252 9 3 7 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 252
  (Polychromatic418967fa.accept_17_9_12_14_1_5423 26 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 252 3 8 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 63 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 22 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 252 21 1 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 63 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 252 9 2 7 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 252
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 16 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 252 3 5 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 63 252 7 2 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 252 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 63
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 252 3 4 21 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 252 (Polychromatic418967fa.accept_20_10_3_12_1_15195 10 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 252 9 1 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 63 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 252 7 1 9 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 63 252 3 2 21 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 252 (Polychromatic418967fa.accept_16_4_15_12_1_1745 4 63 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 252 3 1 21 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 63 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 1 63 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 252 (allA_succ_of_accept
  61 62 252 (accept_3_4 61 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 252 2 30 31 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 252
  (Polychromatic418967fa.accept_15_14_2_12_1_2472 59 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 252 2 29 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 252 (Polychromatic418967fa.accept_20_17_2_12_1_8168 57 62 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 252 2 28 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 252 (accept_3_4 55 62 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 252 2 27 31 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 252
  (Polychromatic418967fa.accept_22_9_18_10_1_7319 53 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 62 252 2 26 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 62 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 51 62 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 62 252 2 25 31 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 62 252 (accept_3_4 49 62 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62 252 2 24 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 62 252 (Polychromatic418967fa.accept_11_3_7_10_1_180
  47 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 252 2 23 31 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 252 2 22 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 252 (accept_3_4 43 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 252 2 21 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643 41 62 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 252 2 20 31 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 252
  (Polychromatic418967fa.accept_20_19_2_12_1_2516 39 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 252 2 19 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 252 (accept_3_4 37 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 252 2 18 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 62 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 252 2 17 31 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 252
  (Polychromatic418967fa.accept_15_3_2_12_1_2469 33 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 252 2 16 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 252 (accept_3_4 31 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 252 2 15 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 252 (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 62 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 252 2 14 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 252
  (Polychromatic418967fa.accept_20_7_2_12_1_6642 27 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 252 2 13 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 252 (accept_3_4 25 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 252 2 12 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 252 (Polychromatic418967fa.accept_25_23_12_2_1_15224 23 62 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 252 2 11 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 252
  (Polychromatic418967fa.accept_13_8_10_5_1_977 21 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 252 2 10 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 252 (accept_3_4 19 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 252 2 9 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 62 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 252 2 8 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 252 (Polychromatic418967fa.accept_13_2_10_5_1_1643
  15 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 252 2 7 31 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 252 (accept_3_4 13
  62 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 252 2 6 31 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 252
  (Polychromatic418967fa.accept_22_11_18_10_1_12179 11 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 252 2 5 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 62 252 (Polychromatic418967fa.accept_20_9_2_12_1_5144 9 62 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 252 2 4 31 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 252 (accept_3_4 7 62 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 252 2 3 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 62 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 62 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 252 2 2 31 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 252
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 252 2 1 31 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 252 (accept_3_4 1 62 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 252 (allA_succ_of_accept 60 61 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 252 (accept_3_5 59 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 58 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 252 (accept_3_5 56 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 55 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 252
  (Polychromatic418967fa.accept_13_2_9_5_1_959 54 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 252 (accept_3_5 53 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 252 (Polychromatic418967fa.accept_16_4_13_12_1_1740 52 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 252 (Polychromatic418967fa.accept_20_11_1_12_1_3803 51 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 252 (accept_3_5 50 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 61 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 252
  (Polychromatic418967fa.accept_22_4_17_10_1_9106 48 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 252 (accept_3_5 47 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 252 (Polychromatic418967fa.accept_27_18_7_9_1_15223 45 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 252 (accept_3_5 44 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 61 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 42 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 252 (accept_3_5 41 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 40 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 252 (accept_3_5 38 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 252 (Polychromatic418967fa.accept_19_18_4_5_1_5723 37 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 252 (accept_3_5 35 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 34 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 252 (accept_3_5 32 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 252 (Polychromatic418967fa.accept_16_15_13_12_1_1787 31 61 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 252
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 30 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 252 (accept_3_5 29 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 28 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 252 (accept_3_5 26 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 61 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 252
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 252 (accept_3_5 23 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 252 (Polychromatic418967fa.accept_17_5_10_14_1_2083 22 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 252 (Polychromatic418967fa.accept_19_2_4_5_1_3021 21 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 252 (accept_3_5 20 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 252
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 18 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 252 (accept_3_5 17 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 252 (accept_3_5 14 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 252
  (Polychromatic418967fa.accept_19_12_4_5_1_9936 12 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 252 (accept_3_5 11 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 252 (Polychromatic418967fa.accept_16_10_13_12_1_4873 10 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 252 (accept_3_5 8 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 252 (Polychromatic418967fa.accept_17_7_10_14_1_8022 7 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 252 (accept_3_5 5 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 61 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 252 (accept_3_5 2 61 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 61 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 252 (allA_succ_of_accept 59 60 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 59 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 252 2 29 30 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 60 252 3 19 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 60 252 4 14 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 60 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 55 60 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 252 6 9 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315
  53 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 252 4 13 15 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 60 252 3 17 20 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 60 252 2 25 30 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 252
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 252 12 4 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 252 (Polychromatic418967fa.accept_22_3_16_10_1_7310 47 60 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 252 2 23 30 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 252 3 15 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 252 4 11 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 252
  (Polychromatic418967fa.accept_25_18_10_2_1_15222 43 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 60 252 6 7 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 60 252 (Polychromatic418967fa.accept_23_18_14_22_1_15221 41 60 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 252 4 10 15 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 252 3 13 20 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 252 2 19 30 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 37 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 252 12 3 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 252 (Polychromatic418967fa.accept_19_16_3_5_1_5684 35 60 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 252 2 17 30 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 60 252 3 11 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 60 252 4 8 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 252
  (Polychromatic418967fa.accept_23_8_14_22_1_12013 31 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 60 252 6 5 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 60 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 29 60 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 252 4 7 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 252 3 9 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 252 2 13 30 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 252
  (Polychromatic418967fa.accept_13_12_8_5_1_976 25 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 252 12 2 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 60 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 252 2 11 30 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 252 3 7 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 252 4 5 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 252
  (Polychromatic418967fa.accept_25_19_10_2_1_15220 19 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 60 252 6 3 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 60 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 60 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 252 4 4 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 252 3 5 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 252 2 7 30 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 252
  (Polychromatic418967fa.accept_23_13_14_22_1_15219 13 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 60 252 12 1 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 60 252 (Polychromatic418967fa.accept_23_11_14_22_1_15218 11 60 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 252 2 5 30 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 252 3 3 20 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 252 4 2 15 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 252
  (Polychromatic418967fa.accept_19_7_3_5_1_8585 7 60 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 252 6 1 10 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 252 (Polychromatic418967fa.accept_17_5_9_14_1_4282 5 60 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 252 4 1 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 252 3 1 20 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 252 2 1 30 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 60 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 252 (allA_succ_of_accept 58 59 252
  (accept_3_4 58 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 56 59 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 252 (accept_3_4 55 59 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 59 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 252
  (Polychromatic418967fa.accept_20_13_19_12_1_5143 53 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 59 252 (accept_3_4 52 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 59 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 59 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 50 59
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 252 (accept_3_4 49 59 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 252 (Polychromatic418967fa.accept_19_10_2_5_1_3059
  48 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 252 (accept_3_4 46 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 252 (Polychromatic418967fa.accept_17_11_8_14_1_8084 45 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 252 (Polychromatic418967fa.accept_24_20_11_12_1_15217 44 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 252 (accept_3_4 43 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 252 (Polychromatic418967fa.accept_16_10_11_12_1_4835 42 59
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 252 (accept_3_4 40 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 38 59 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 252 (accept_3_4 37 59 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 252 (Polychromatic418967fa.accept_16_4_11_12_1_1775 36 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 252
  (Polychromatic418967fa.accept_19_16_2_5_1_5681 35 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 252 (accept_3_4 34 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 252 (Polychromatic418967fa.accept_16_1_11_12_1_1774 33 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 252 (Polychromatic418967fa.accept_15_2_14_12_1_2453 32 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 252 (accept_3_4 31 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 252 (Polychromatic418967fa.accept_24_6_11_12_1_15216 30 59
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 252
  (Polychromatic418967fa.accept_19_10_2_5_1_3059 29 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 252 (accept_3_4 28 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 252 (accept_3_4 25 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 59
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 252 (accept_3_4 22 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 252 (Polychromatic418967fa.accept_16_4_11_12_1_1775 20 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 252 (accept_3_4 19 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 252 (Polychromatic418967fa.accept_19_18_2_5_1_5682 18 59
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 252 (accept_3_4 16 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 252 (Polychromatic418967fa.accept_19_14_2_5_1_9949 14 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 252 (accept_3_4 13 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 252 (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 59
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 252 (accept_3_4 10 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 252 (Polychromatic418967fa.accept_16_8_11_12_1_962 8 59 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 252 (accept_3_4 7 59 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 252 (Polychromatic418967fa.accept_17_6_8_14_1_6706 6 59 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 252 (accept_3_4 4 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  252 (Polychromatic418967fa.accept_19_3_2_5_1_5679 3 59 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 59 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 252 (accept_3_4 1 59 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 252
  (allA_succ_of_accept 57 58 252 (Polychromatic418967fa.accept_17_6_7_14_1_6704 57 58 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 252 2 28 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 55
  58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 252 2 27 29 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 252 (accept_3_5 53
  58 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 252 2 26 29 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 58 252 2 25 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 58 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 49 58 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 252 2 24 29 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 252 (accept_3_5 47 58 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 252 2 23 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 45
  58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 252 2 22 29 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 252
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 43 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 252 2 21 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 58 252 (accept_3_5 41 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 58 252 2 20 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 58 252 (Polychromatic418967fa.accept_26_13_6_18_1_15215 39 58 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 252 2 19 29 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 252
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 37 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 252 2 18 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 58 252 (accept_3_5 35 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 58 252 2 17 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 58 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 33 58 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 252 2 16 29 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 252
  (Polychromatic418967fa.accept_15_1_13_12_1_347 31 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 252 2 15 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 58 252 (accept_3_5 29 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 58 252 2 14 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 58 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 252 2 13 29 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 252 2 12 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 58 252 (accept_3_5 23 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 58 252 2 11 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 252 (Polychromatic418967fa.accept_16_5_10_12_1_4904 21 58 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 252 2 10 29 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 252
  (Polychromatic418967fa.accept_16_3_10_12_1_4814 19 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 252 2 9 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 252 (accept_3_5 17 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  252 2 8 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 252 2 7 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 58 252 (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 58 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 252 2 6 29 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 252 (accept_3_5 11 58 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 252 2 5 29 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 252
  (Polychromatic418967fa.accept_19_9_1_5_1_11278 9 58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 252 2 4 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 58 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 252 2 3 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 252 (accept_3_5 5 58 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 252 2 2 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 58 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 252 2 1 29 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 1
  58 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 252 (allA_succ_of_accept 56 57 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 57 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 252 3 18 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 53
  57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 252
  (Polychromatic418967fa.accept_16_4_9_12_1_4829 52 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 252 3 17 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 252 (Polychromatic418967fa.accept_16_2_9_12_1_46 50 57 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 49 57 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 252 3 16 19 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 252
  (Polychromatic418967fa.accept_20_7_17_12_1_11156 47 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 252 (Polychromatic418967fa.accept_20_6_17_12_1_8210 46 57 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 252 3 15 19 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 252 (Polychromatic418967fa.accept_22_21_13_10_1_12154 43 57 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 252 3 14 19 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 252
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 41 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 252 (Polychromatic418967fa.accept_16_8_9_12_1_1737 40 57 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 252 3 13 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 252
  (Polychromatic418967fa.accept_23_15_11_22_1_12009 38 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 57 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 57 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 252 3 12 19 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 35 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 57 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 252 3 11 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 252 (Polychromatic418967fa.accept_17_15_6_14_1_4239
  32 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 252
  (Polychromatic418967fa.accept_22_9_13_10_1_15214 31 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 57 252 3 10 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 57 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 57 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 252
  (Polychromatic418967fa.accept_27_1_3_9_1_15213 28 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 57 252 3 9 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 57 252 (Polychromatic418967fa.accept_20_6_17_12_1_8210 26 57 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 57 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 252 3 8 19 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 252 (Polychromatic418967fa.accept_20_2_17_12_1_5178 22 57 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 252 3 7 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 252 (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 57 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 19 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 57 252 3 6 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 57 252 (Polychromatic418967fa.accept_27_17_3_9_1_13394 17 57 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 252 (Polychromatic418967fa.accept_26_16_5_18_1_15212 16 57
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 252 3 5 19 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 57 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 252 3 4 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 252 (Polychromatic418967fa.accept_24_11_9_12_1_15211 11 57
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 252
  (Polychromatic418967fa.accept_23_10_11_22_1_8745 10 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 57 252 3 3 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 57 252 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 57 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 252 (Polychromatic418967fa.accept_17_7_6_14_1_6737
  7 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 252 3 2 19 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 57 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 252 3 1 19 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 252 (Polychromatic418967fa.accept_16_2_9_12_1_46 2 57 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 57 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 252 (allA_succ_of_accept 55 56
  252 (accept_3_4 55 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 56 252 2 27 28 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 56 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 53 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 56 252 4 13 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 56 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 56 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 252 2 25 28 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 56 252 7 7 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 56 252 4 12 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 252 (Polychromatic418967fa.accept_16_15_8_12_1_2737
  47 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 252 2 23 28 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 252 4 11 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 56 252 (accept_3_4 43 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  252 14 3 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 56 252 4 10 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 56 252 (Polychromatic418967fa.accept_16_7_8_12_1_4902 39 56 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 252 2 19 28 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 252 (accept_3_4 37 56 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 252 4 9 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 56 252 7 5 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 56 252 2 17 28 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 252
  (Polychromatic418967fa.accept_16_1_8_12_1_405 33 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 252 4 8 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 252 (accept_3_4 31 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  252 2 15 28 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 56 252 (Polychromatic418967fa.accept_15_14_11_12_1_4440 29 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 252 28 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 56 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 252 2 13 28 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 252 (accept_3_4 25 56 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 252 4 6 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 56 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 252 2 11 28 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 56 252 7 3 8 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 56 252 4 5 14 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 252 (accept_3_4 19
  56 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 252 2 9 28 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 252
  (Polychromatic418967fa.accept_16_1_8_12_1_405 17 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 56 252 4 4 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 56 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 56 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 252 14 1 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 252 (accept_3_4 13 56 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 56 252 4 3 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 56 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 252 2 5 28 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 56 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 252 4 2 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 56 252 7 1 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 56 252 2 3 28 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 56 252 (Polychromatic418967fa.accept_16_5_8_12_1_1766 5 56 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 252 4 1 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 252 (Polychromatic418967fa.accept_16_3_8_12_1_2736 3 56 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 252 2 1 28 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 252 (accept_3_4 1 56 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 252))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 252 (allA_succ_of_accept 54 55 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 252 (accept_3_5 53 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 55
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 252 (accept_3_5 50 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 252 (Polychromatic418967fa.accept_19_11_17_5_1_8609 49 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 55 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 252 (accept_3_5 47 55 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 252 (Polychromatic418967fa.accept_20_6_15_12_1_6637 46 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 252
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 252 (accept_3_5 44 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 252 (Polychromatic418967fa.accept_23_19_9_22_1_15210 42 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 252 (accept_3_5 41 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 40 55 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 252 (accept_3_5 38 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 252 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 252 (accept_3_5 35 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 34 55 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 33 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 252 (accept_3_5 32 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 252 (Polychromatic418967fa.accept_19_12_17_5_1_5702 31 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 252 (Polychromatic418967fa.accept_17_13_4_14_1_4272 30 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 252 (accept_3_5 29 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 55 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 252 (accept_3_5 26 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 252 (Polychromatic418967fa.accept_20_5_15_12_1_9720 25 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 55 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 252 (accept_3_5 23 55 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 22 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 252
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 252 (accept_3_5 20 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 55 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 252 (accept_3_5 17 55 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 252 (Polychromatic418967fa.accept_24_16_7_12_1_15209 16 55 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 252
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 252 (accept_3_5 14 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 252 (Polychromatic418967fa.accept_19_12_17_5_1_5702 12 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 252 (accept_3_5 11 55 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 252 (Polychromatic418967fa.accept_20_10_15_12_1_11131 10 55
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 252
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 252 (accept_3_5 8 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  252 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 252 (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 55 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 252 (accept_3_5 5 55 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 252 (Polychromatic418967fa.accept_16_4_7_12_1_2734 4 55 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 55
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 252 (accept_3_5 2 55 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 1
  55 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  252))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 252 (allA_succ_of_accept 53 54 252
  (Polychromatic418967fa.accept_17_2_3_14_1_8043 53 54 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 252 2 26 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 54 252 3 17 18 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 54 252 2 25 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 54 252 (Polychromatic418967fa.accept_13_10_2_5_1_1633 49 54 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 252 6 8 9 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 54 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 252 2 23 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 54 252 9 5 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 54 252 2 22 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 54 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 43 54 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 252 6 7 9 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 252
  (Polychromatic418967fa.accept_19_3_16_5_1_7098 41 54 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 252 2 20 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 54 252 3 13 18 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 54 252 2 19 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 54 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 252 18 2 3 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 252
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 54 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 252 2 17 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 54 252 3 11 18 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 54 252 2 16 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 54 252 (Polychromatic418967fa.accept_19_12_16_5_1_12620 31 54 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 252 6 5 9 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 252
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 29 54 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 252 2 14 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 54 252 9 3 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 54 252 2 13 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 54 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 25 54 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 252 6 4 9 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 252
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 54 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 252 2 11 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 54 252 3 7 18 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 54 252 2 10 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 54 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 252 18 1 3 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 54 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 54 252 2 8 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 54 252 3 5 18 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 54 252 2 7 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 252 (Polychromatic418967fa.accept_23_13_8_22_1_15208 13 54 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 252 6 2 9 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 252 (Polychromatic418967fa.accept_17_11_3_14_1_6736 11 54
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 252 2 5 27 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 252 9 1 6 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 252 2 4 27 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 252 6 1 9 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 54 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 252 2 2 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 252 3 1 18 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 252 2 1 27 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 252 (Polychromatic418967fa.accept_19_1_16_5_1_5671 1 54 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 252 (allA_succ_of_accept 52 53 252 (accept_3_4
  52 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 51 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 252 (Polychromatic418967fa.accept_15_5_8_12_1_2435 50 53 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 252 (accept_3_4 49 53 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 48 53 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176
  47 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 252 (accept_3_4 46
  53 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 45 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 252 (Polychromatic418967fa.accept_19_6_15_5_1_5697 44 53 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 252 (accept_3_4 43 53 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 53 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 41
  53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 252 (accept_3_4 40 53
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 252
  (Polychromatic418967fa.accept_16_7_5_12_1_4824 39 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 252 (Polychromatic418967fa.accept_13_12_1_5_1_1650 38 53 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 252 (accept_3_4 37 53 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 252 (Polychromatic418967fa.accept_16_4_5_12_1_2749 36 53 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 252 (accept_3_4 34 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 252 (Polychromatic418967fa.accept_13_6_1_5_1_3988 32 53 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 252 (accept_3_4 31 53 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 53 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 252
  (Polychromatic418967fa.accept_13_3_1_5_1_499 29 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 252 (accept_3_4 28 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 252 (Polychromatic418967fa.accept_22_5_9_10_1_15207 27 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 252 (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 53 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 252 (accept_3_4 25 53 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 252 (Polychromatic418967fa.accept_16_8_5_12_1_3812 24 53
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 252 (accept_3_4 22 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 252 (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 53 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 252 (accept_3_4 19 53 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 53 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 252 (accept_3_4 16 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 252 (Polychromatic418967fa.accept_25_14_3_2_1_15206 14 53 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 252 (accept_3_4 13 53 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 53 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 252 (accept_3_4 10 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 53 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 252 (accept_3_4 7 53 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 252 (Polychromatic418967fa.accept_13_6_1_5_1_3988 6 53 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 252 (accept_3_4 4 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  252 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 53 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 252 (Polychromatic418967fa.accept_26_2_1_18_1_11702 2 53 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 252 (accept_3_4 1 53 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 252))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 252
  (allA_succ_of_accept 51 52 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 51 52 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 252 2 25 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 252 (Polychromatic418967fa.accept_15_4_7_12_1_5538
  49 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 252 4 12 13 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 252 (accept_3_5 47
  52 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 252 2 23 26 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 252
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 252 4 11 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 252 (Polychromatic418967fa.accept_16_11_4_12_1_1760 43 52 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 252 2 21 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 252 (accept_3_5 41 52 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 252 4 10 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 52 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 252 2 19 26 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 252
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 37 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 252 4 9 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 252 (accept_3_5 35 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  252 2 17 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 52 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 252 4 8 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 52 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 52 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 252 2 15 26 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 252 (accept_3_5 29 52 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 252 4 7 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 252 (Polychromatic418967fa.accept_16_11_4_12_1_1760 27 52
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 252 2 13 26 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 252
  (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 252 4 6 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 252 (accept_3_5 23 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  252 2 11 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 52 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 21 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 252 4 5 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 52 252 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 52 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 252 2 9 26 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 252 (accept_3_5 17 52 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 252 4 4 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 252 (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 52
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 252 2 7 26 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 252
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 252 4 3 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 252 (accept_3_5 11 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  252 2 5 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 252 4 2 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 7 52 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 252 2 3 26 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 252 (accept_3_5 5 52 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 252 4 1 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 52 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 252 2 1 26 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 252
  (Polychromatic418967fa.accept_16_1_4_12_1_376 1 52 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 252)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 252 (allA_succ_of_accept 50 51 252
  (Polychromatic418967fa.accept_15_5_6_12_1_916 50 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 252 3 16 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 47
  51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 46 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 252 3 15 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 252 (Polychromatic418967fa.accept_23_21_5_22_1_15205 44 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 51 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 252 3 14 17 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 40 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 252 3 13 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 252 (Polychromatic418967fa.accept_22_16_7_10_1_7356
  38 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 252 3 12 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 34 51
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 252 3 11 17 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 252 3 10 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 29
  51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 28 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 252 3 9 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 51 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 252 3 8 17 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 252 (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 252 3 7 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603 20 51 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 19 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 252 3 6 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 51 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 252 3 5 17 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 252
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 252 3 4 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 252 (Polychromatic418967fa.accept_19_11_13_5_1_5714 11 51
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 252
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 252 3 3 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 51 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 252 3 2 17 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 252
  (Polychromatic418967fa.accept_15_5_6_12_1_916 5 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 51 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 252 3 1 17 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 252 (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 51 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 252
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 51 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 252))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 252 (allA_succ_of_accept 49 50 252
  (accept_3_4 49 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 252 2 24 25 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 252
  (Polychromatic418967fa.accept_15_2_5_12_1_369 47 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 252 2 23 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 50 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 45 50 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 252 2 22 25 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 252 (accept_3_4 43 50 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 252 2 21 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800
  41 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 252 2 20 25 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 252
  (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 252 2 19 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 50 252 (accept_3_4 37 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 252 2 18 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 252 (Polychromatic418967fa.accept_19_16_12_5_1_8578 35 50 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 252 2 17 25 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 252
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 252 2 16 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 252 (accept_3_4 31 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 252 2 15 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 50 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 252 2 14 25 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 252 2 13 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 252 (accept_3_4 25 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 252 2 12 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 252 (Polychromatic418967fa.accept_15_8_5_12_1_4453 23 50 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 252 2 11 25 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 252
  (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 252 2 10 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 252 (accept_3_4 19 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 252 2 9 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 252 (Polychromatic418967fa.accept_15_2_5_12_1_369 17 50 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 252 2 8 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 252 (Polychromatic418967fa.accept_16_15_2_12_1_1799
  15 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 252 2 7 25 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 252 (accept_3_4 13
  50 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 252 2 6 25 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 252
  (Polychromatic418967fa.accept_17_11_16_14_1_6760 11 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 252 2 5 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 50 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 50 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 252 2 4 25 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 252 (accept_3_4 7 50 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 252 2 3 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 50 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 252 2 2 25 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 252
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 252 2 1 25 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 252 (accept_3_4 1 50 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  252)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 252 (allA_succ_of_accept 48 49 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 48 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 49 252 (accept_3_5 47 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  49 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 46 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 49 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 49 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 252 (accept_3_5 44 49 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 43 49 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 49 252 7 6 7 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 49 252 (accept_3_5 41 49 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 252 (Polychromatic418967fa.accept_16_8_1_12_1_984 40 49 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 39 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 252 (accept_3_5 38 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 252 (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 49 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 49 252 7 5 7 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 49 252
  (Polychromatic418967fa.accept_13_8_10_5_1_977 34 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 49 252 (Polychromatic418967fa.accept_17_16_15_14_1_6747 33 49 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 252 (accept_3_5 32 49 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 49 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 49 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644
  30 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 252 (accept_3_5 29
  49 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49 252 7 4 7 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 49 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 252 (accept_3_5 26 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 252 (Polychromatic418967fa.accept_19_6_11_5_1_5628 25 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 24 49 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 252 (accept_3_5 23 49 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 252 (Polychromatic418967fa.accept_15_7_4_12_1_2530 22 49
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 49 252 7 3 7 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 49 252 (accept_3_5 20
  49 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 252 (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 49 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 252 (accept_3_5 17 49 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 252 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 49 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 49 252 7 2 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 49 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 252 (Polychromatic418967fa.accept_17_12_15_14_1_6746 12 49
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 252 (accept_3_5 11 49 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 252
  (Polychromatic418967fa.accept_19_10_11_5_1_7093 10 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 49 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 49 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 252 (accept_3_5 8 49 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 49 252 7 1 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 49 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 49 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 252 (accept_3_5 5 49 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 49 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 252
  (Polychromatic418967fa.accept_17_3_15_14_1_4219 3 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 252 (accept_3_5 2 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  252 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 49 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 252))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 252 (allA_succ_of_accept 47 48 252
  (Polychromatic418967fa.accept_15_2_3_12_1_891 47 48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 252 2 23 24 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 48 252 3 15 16 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 48 252 4 11 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 48 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 43 48 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 252 6 7 8 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 41
  48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 252 4 10 12 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 252 3 13 16 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 252 2 19 24 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 37 48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 252 12 3 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 48 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 252 2 17 24 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 48 252 3 11 16 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 48 252 4 8 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 252 (Polychromatic418967fa.accept_27_4_21_9_1_15204
  31 48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 252 6 5 8 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 29 48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 48 252 4 7 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 48 252 3 9 16 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 48 252 2 13 24 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 48 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 48 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 252 12 2 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657
  23 48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 252 2 11 24 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 252 3 7 16 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 252 4 5 12 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 252
  (Polychromatic418967fa.accept_23_19_2_22_1_13695 19 48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 48 252 6 3 8 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 48 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 48 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 252 4 4 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 48 252 3 5 16 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 48 252 2 7 24 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 252 (Polychromatic418967fa.accept_15_13_3_12_1_1609
  13 48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 252 12 1 4 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 252
  (Polychromatic418967fa.accept_19_11_10_5_1_5662 11 48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 252 2 5 24 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 48 252 3 3 16 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 48 252 4 2 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 48 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 252 6 1 8 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 48 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 252 4 1 12 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 252 3 1 16 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 252 2 1 24 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 252
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 48 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 252)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 252 (allA_succ_of_accept 46 47 252
  (accept_3_4 46 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 45 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 47 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 252 (accept_3_4 43 47 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 42 47 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 252
  (Polychromatic418967fa.accept_23_18_1_22_1_15203 41 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 47 252 (accept_3_4 40 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 47 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 47 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 38 47 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 252 (accept_3_4 37 47 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616
  36 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 252 (accept_3_4 34 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 33 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 252 (Polychromatic418967fa.accept_19_13_9_5_1_8541 32 47 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 252 (accept_3_4 31 47 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 252 (Polychromatic418967fa.accept_23_7_1_22_1_15202 30 47
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 252
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 252 (accept_3_4 28 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 252 (Polychromatic418967fa.accept_19_7_9_5_1_8590 26 47 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 252 (accept_3_4 25 47 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 47 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 252
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 252 (accept_3_4 22 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 20 47 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 252 (accept_3_4 19 47 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 47
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 252
  (Polychromatic418967fa.accept_20_17_7_12_1_6632 17 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 252 (accept_3_4 16 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 47 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 252 (accept_3_4 13 47 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 47 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 252 (accept_3_4 10 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 47 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 252 (accept_3_4 7 47 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 6 47 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 252 (accept_3_4 4 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 47 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744 2 47 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 252 (accept_3_4 1 47 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 252))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 252 (allA_succ_of_accept 45
  46 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 252 2 22 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 43 46 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 252 2 21 23 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 252 (accept_3_5 41 46 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 252 2 20 23 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 252
  (Polychromatic418967fa.accept_25_14_21_2_1_15201 39 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 46 252 2 19 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 46 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 46 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 252 2 18 23 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 252 (accept_3_5 35 46 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 252 2 17 23 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 252
  (Polychromatic418967fa.accept_19_14_8_5_1_8606 33 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 252 2 16 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 46 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 31 46 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 252 2 15 23 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 252 (accept_3_5 29 46 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 252 2 14 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 252 (Polychromatic418967fa.accept_20_7_6_12_1_6650
  27 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 252 2 13 23 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 252
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 25 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 252 2 12 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 46 252 (accept_3_5 23 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 46 252 2 11 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 46 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 252 2 10 23 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 252
  (Polychromatic418967fa.accept_15_4_1_12_1_914 19 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 252 2 9 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 252 (accept_3_5 17 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  252 2 8 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 252 2 7 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 46 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 46 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 252 2 6 23 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 252 (accept_3_5 11 46 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 252 2 5 23 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 252
  (Polychromatic418967fa.accept_17_9_12_14_1_5423 9 46 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 252 2 4 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 252 (Polychromatic418967fa.accept_20_7_6_12_1_6650 7 46 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 252 2 3 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 252 (accept_3_5 5 46 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 252 2 2 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 252 (Polychromatic418967fa.accept_19_3_8_5_1_1875 3 46 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 252 2 1 23 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  46 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  252)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 252 (allA_succ_of_accept 44 45 252
  (Polychromatic418967fa.accept_19_6_7_5_1_256 44 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 45 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 252 3 14 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 41
  45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 252
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 40 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 252 3 13 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 45 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 45 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 252 9 4 5 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 35 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 252 (Polychromatic418967fa.accept_25_9_20_2_1_15200 34 45 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 252 3 11 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 252 (Polychromatic418967fa.accept_19_13_7_5_1_5712
  32 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 31 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 252 3 10 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 45 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 45 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 252 9 3 5 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 252
  (Polychromatic418967fa.accept_16_10_13_12_1_4873 26 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 45 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 45 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 252 3 8 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 23
  45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 252
  (Polychromatic418967fa.accept_19_3_7_5_1_12632 22 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 252 3 7 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 45 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 252 (Polychromatic418967fa.accept_22_19_1_10_1_15199 19 45
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 252 9 2 5 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 16 45 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 252 3 5 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 45 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 13 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 252 3 4 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 45 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 45
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 252 9 1 5 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 45 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 252 3 2 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 252 (Polychromatic418967fa.accept_22_5_1_10_1_15198 5 45 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 252
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 45 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 252 3 1 15 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 2 45 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 45 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  252))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 252 (allA_succ_of_accept 43 44 252 (accept_3_4 43 44
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 252 2 21 22 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 252
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 41 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 252 4 10 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 44 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 252 2 19 22 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 252 (accept_3_4 37 44 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 252 4 9 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 252 (Polychromatic418967fa.accept_17_1_10_14_1_1173
  35 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 252 2 17 22 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 252
  (Polychromatic418967fa.accept_19_14_6_5_1_9917 33 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 252 4 8 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 252 (accept_3_4 31 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  252 2 15 22 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 44 252 (Polychromatic418967fa.accept_23_6_21_22_1_13684 29 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 252 4 7 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 44 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 252 2 13 22 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 252 (accept_3_4 25 44 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 252 4 6 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 252 (Polychromatic418967fa.accept_19_4_6_5_1_11350 23 44 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 252 2 11 22 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 252
  (Polychromatic418967fa.accept_25_21_19_2_1_15197 21 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 44 252 4 5 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 44 252 (accept_3_4 19 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 44 252 2 9 22 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 44 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 44 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 252 4 4 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 252 (Polychromatic418967fa.accept_19_15_6_5_1_4356 15 44 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 252 2 7 22 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 252 (accept_3_4 13
  44 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 252 4 3 11 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 252
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 252 2 5 22 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 44 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 44 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 252 4 2 11 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 252 (accept_3_4 7 44 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 252 2 3 22 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44 252 (Polychromatic418967fa.accept_17_5_10_14_1_2083 5 44 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 252 4 1 11 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 252
  (Polychromatic418967fa.accept_19_3_6_5_1_9947 3 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 252 2 1 22 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 252 (accept_3_4 1 44 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  252)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 252 (allA_succ_of_accept 42 43 252
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 42 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 43 252 (accept_3_5 41 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 43 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 40 43 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 43 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 252 (accept_3_5 38 43 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 252
  (Polychromatic418967fa.accept_25_12_18_2_1_15196 37 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 252 (accept_3_5 35 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 252 (Polychromatic418967fa.accept_23_11_20_22_1_7070 34 43
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 33 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 252 (accept_3_5 32 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 252 (Polychromatic418967fa.accept_20_10_3_12_1_15195 30 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 252 (accept_3_5 29 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 43 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 252
  (Polychromatic418967fa.accept_13_1_4_5_1_113 27 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 252 (accept_3_5 26 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 252 (Polychromatic418967fa.accept_16_8_11_12_1_962 24 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 252 (accept_3_5 23 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 22 43 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 21 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 252 (accept_3_5 20 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 18 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 252 (accept_3_5 17 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 252 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 43
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 252 (accept_3_5 14 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 252 (Polychromatic418967fa.accept_20_13_3_12_1_15194 13 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 252 (accept_3_5 11 43 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 43
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 252
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 252 (accept_3_5 8 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 43 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 252 (accept_3_5 5 43 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 252 (Polychromatic418967fa.accept_16_4_11_12_1_1775 4 43 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 252 (Polychromatic418967fa.accept_15_3_13_12_1_348
  3 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 252 (accept_3_5 2 43
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 1 43 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 252))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 252 (allA_succ_of_accept 41 42 252
  (Polychromatic418967fa.accept_11_8_9_10_1_503 41 42 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 252 2 20 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 42 252 3 13 14 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 42 252 2 19 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 42 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 37 42 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 252 6 6 7 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 252 7 5 6 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 42 252 2 17 21 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 252 3 11 14 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 42 252 2 16 21 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 252
  (Polychromatic418967fa.accept_19_12_4_5_1_9936 31 42 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 252 6 5 7 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 252 (Polychromatic418967fa.accept_16_13_10_12_1_1811 29 42 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 252 14 2 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 252 3 9 14 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 42 252 2 13 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 252 (Polychromatic418967fa.accept_19_6_4_5_1_5650
  25 42 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 252 6 4 7 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 42 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 252 2 11 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 42 252 21 1 2 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 42 252 2 10 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 42 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 252 6 3 7 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 252
  (Polychromatic418967fa.accept_20_17_2_12_1_8168 17 42 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 252 2 8 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 42 252 3 5 14 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 252 14 1 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 252 (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 42 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 252 6 2 7 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 42 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 252 2 5 21 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 42 252 3 3 14 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 42 252 2 4 21 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 42 252 7 1 6 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 252 6 1 7 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 252
  (Polychromatic418967fa.accept_16_5_10_12_1_4904 5 42 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 252 2 2 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 42 252 3 1 14 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 42 252 2 1 21 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 42 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 252)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 252
  (allA_succ_of_accept 40 41 252 (accept_3_4 40 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 38 41 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 252 (accept_3_4 37 41 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 41 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 252
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 252 (accept_3_4 34 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 252 (Polychromatic418967fa.accept_24_8_17_12_1_15193 32 41 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 252 (accept_3_4 31 41 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 41 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 252 (accept_3_4 28 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 252 (Polychromatic418967fa.accept_17_10_7_14_1_4244 27 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 41 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 252 (accept_3_4 25 41 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 252 (Polychromatic418967fa.accept_16_8_9_12_1_1737 24 41 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 252 (accept_3_4 22 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 20 41 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 252 (accept_3_4 19 41 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 252 (Polychromatic418967fa.accept_16_2_9_12_1_46 18 41 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 252
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 252 (accept_3_4 16 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 252 (Polychromatic418967fa.accept_24_15_17_12_1_662 15 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 252 (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 41 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 252 (accept_3_4 13 41 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 41
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 252
  (Polychromatic418967fa.accept_20_11_1_12_1_3803 11 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 252 (accept_3_4 10 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 252 (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 41 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 252 (accept_3_4 7 41 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 41 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 252 (accept_3_4 4 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  252 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 41 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 252 (Polychromatic418967fa.accept_16_2_9_12_1_46 2 41 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 252 (accept_3_4 1 41 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 252))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 252 (allA_succ_of_accept 39 40 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 40 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 252 2 19 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 40 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 37 40 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 252 4 9 10 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 252 (accept_3_5 35 40 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 252 2 17 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 252 (Polychromatic418967fa.accept_16_1_8_12_1_405
  33 40 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 252 4 8 10 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 252
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 31 40 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 252 2 15 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 40 252 (accept_3_5 29 40 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 40 252 4 7 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 40 252 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 40 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 252 2 13 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 252 (Polychromatic418967fa.accept_11_3_7_10_1_180
  25 40 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 252 4 6 10 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 252 (accept_3_5 23
  40 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 252 2 11 20 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 252
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 40 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 252 4 5 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 252 (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 40 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 252 2 9 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 252 (accept_3_5 17 40 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 252 4 4 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 40 252 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 40 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 252 2 7 20 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 252
  (Polychromatic418967fa.accept_15_13_10_12_1_2503 13 40 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 40 252 4 3 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 40 252 (accept_3_5 11 40 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 40 252 2 5 20 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 40 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 40 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 252 4 2 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 40 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 252 2 3 20 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 252 (accept_3_5 5 40 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 252 4 1 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 3
  40 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 252 2 1 20 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 252
  (Polychromatic418967fa.accept_16_1_8_12_1_405 1 40 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 252)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 252 (allA_succ_of_accept 38 39 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 39 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 252 3 12 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 35
  39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 252
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 34 39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 252 3 11 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 252 (Polychromatic418967fa.accept_26_6_13_18_1_15192 32 39 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 39 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 252 3 10 13 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 252
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 252 (Polychromatic418967fa.accept_19_9_1_5_1_11278 28 39 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 252 3 9 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 252 (Polychromatic418967fa.accept_17_9_5_14_1_4277 26 39 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 252
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 252 3 8 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 252 (Polychromatic418967fa.accept_19_4_1_5_1_9933 23 39 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 252 (Polychromatic418967fa.accept_19_3_1_5_1_8549 22 39 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 252 3 7 13 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 252
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 39 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 252 3 6 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 39 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 252 3 5 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 252 (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 39 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 252 (Polychromatic418967fa.accept_20_13_19_12_1_5143 13 39
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 252 3 4 13 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 252 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 39 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 252 3 3 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 252 (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 39 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 252 3 2 13 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 39 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 39 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 252 3 1 13 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 252
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 2 39 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 39 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 252))))))))))))))))))))))))))))))))))))))) (allB_succ 38 252
  (allA_succ_of_accept 37 38 252 (accept_3_4 37 38 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  252 2 18 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 38 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 252 2 17 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603 33 38 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 252 2 16 19 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 252 (accept_3_4 31 38 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 252 2 15 19 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 252
  (Polychromatic418967fa.accept_22_7_16_10_1_7361 29 38 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 252 2 14 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 38 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 252 2 13 19 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 252 (accept_3_4 25 38 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 252 2 12 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 252 (Polychromatic418967fa.accept_25_23_13_2_1_8183
  23 38 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 252 2 11 19 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 252
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 38 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 252 2 10 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 38 252 (accept_3_4 19 38 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 252 2 9 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 252 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 38 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 252 2 8 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 15
  38 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 252 2 7 19 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 252 (accept_3_4 13
  38 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 252 2 6 19 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 252
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 38 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 252 2 5 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 252 (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 38 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 252 2 4 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 252 (accept_3_4 7 38 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 252 2 3 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 38 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 252 2 2 19 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 3
  38 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 252 2 1 19 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 252 (accept_3_4 1 38
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 252)))))))))))))))))))))))))))))))))))))) (allB_succ 37 252
  (allA_succ_of_accept 36 37 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 36 37 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 252 (accept_3_5 35 37 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 37 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 33
  37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 252 (accept_3_5 32 37
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 252
  (Polychromatic418967fa.accept_23_8_14_22_1_12013 31 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 252 (Polychromatic418967fa.accept_24_6_13_12_1_15178 30 37 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 252 (accept_3_5 29 37 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 252 (Polychromatic418967fa.accept_17_11_3_14_1_6736 28 37
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 252 (accept_3_5 26 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 37 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 252 (accept_3_5 23 37 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 252 (Polychromatic418967fa.accept_20_2_17_12_1_5178 22 37 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 252
  (Polychromatic418967fa.accept_15_6_7_12_1_869 21 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 252 (accept_3_5 20 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 18 37 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 252 (accept_3_5 17 37 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 37 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 15 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 252 (accept_3_5 14 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 252 (Polychromatic418967fa.accept_19_13_18_5_1_8619 13 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 252 (Polychromatic418967fa.accept_22_12_15_10_1_12144 12 37 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 252 (accept_3_5 11 37 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 252 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 37
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 252 (accept_3_5 8 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 37 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 252 (accept_3_5 5 37 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 37 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 252
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 252 (accept_3_5 2 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 37 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 252))))))))))))))))))))))))))))))))))))) (allB_succ 36 252 (allA_succ_of_accept 35 36 252
  (Polychromatic418967fa.accept_15_5_6_12_1_916 35 36 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 252 2 17 18 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 36 252 3 11 12 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 36 252 4 8 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 36 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 31 36 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 252 6 5 6 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  29 36 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 252 4 7 9 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 36 252 9 3 4 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 36 252 2 13 18 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 252
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 36 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 252 12 2 3 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 36 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 252 2 11 18 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 36 252 3 7 12 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 36 252 4 5 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 252 (Polychromatic418967fa.accept_13_6_10_5_1_1648
  19 36 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 252 18 1 2 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 36 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 36 252 4 4 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 36 252 3 5 12 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 36 252 2 7 18 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 252 (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 36 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 252 12 1 3 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 36 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 252 2 5 18 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 252 9 1 4 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 252 4 2 9 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 252
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 36 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 252 6 1 6 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 36 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 252 4 1 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 36 252 3 1 12 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 36 252 2 1 18 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 252))))))))))))))))))))))))))))))))))))
  (allB_succ 35 252 (allA_succ_of_accept 34 35 252 (accept_3_4 34 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 35 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 252 (Polychromatic418967fa.accept_15_2_5_12_1_369 32 35 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 252 (accept_3_4 31 35 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641
  30 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 29 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 35 252 7 4 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 35 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 35 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 252 (Polychromatic418967fa.accept_16_10_3_12_1_1758 26 35
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 252 (accept_3_4 25 35 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640
  24 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 252 (accept_3_4 22 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35
  252 7 3 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  35 252 (Polychromatic418967fa.accept_16_4_3_12_1_4892 20 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 35 252 (accept_3_4 19 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 35 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 252 (accept_3_4 16 35 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15
  35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 252 7 2 5 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 252 (accept_3_4 13
  35 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 252 (Polychromatic418967fa.accept_19_11_16_5_1_5667 11 35 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 252 (accept_3_4 10 35 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 35 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 35 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 8
  35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 252 7 1 5 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 252
  (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 252 (Polychromatic418967fa.accept_20_5_15_12_1_9720 5 35 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 252 (accept_3_4 4 35 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 35 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 2
  35 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 252 (accept_3_4 1 35 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 252))))))))))))))))))))))))))))))))))) (allB_succ 34 252
  (allA_succ_of_accept 33 34 252 (Polychromatic418967fa.accept_16_1_2_12_1_1757 33 34 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 252 2 16 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 252 (Polychromatic418967fa.accept_11_9_1_10_1_920
  31 34 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 252 2 15 17 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 252
  (accept_3_5 29 34 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 252 2 14 17 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 34 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 34 252 2 13 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 34 252 (Polychromatic418967fa.accept_13_12_8_5_1_976 25 34 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 252 2 12 17 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 252 (accept_3_5 23 34 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 252 2 11 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 252 (Polychromatic418967fa.accept_25_21_9_2_1_15191
  21 34 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 252 2 10 17 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 252
  (Polychromatic418967fa.accept_23_19_11_22_1_15190 19 34 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 34 252 2 9 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 34 252 (accept_3_5 17 34 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 34 252 2 8 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 34 252 (Polychromatic418967fa.accept_16_15_2_12_1_1799 15 34 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 252 2 7 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 252 (Polychromatic418967fa.accept_11_2_1_10_1_196
  13 34 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 252 2 6 17 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 252 (accept_3_5 11
  34 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 252 2 5 17 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 34 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 252 2 4 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 34 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 252 2 3 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 252 (accept_3_5 5 34 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 252 2 2 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 3 34 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 252 2 1 17 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 252 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1
  34 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 252))))))))))))))))))))))))))))))))))
  (allB_succ 33 252 (allA_succ_of_accept 32 33 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 32 33 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 252
  (Polychromatic418967fa.accept_10_1_3_2_1_220 31 33 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 252 3 10 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 33 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 28 33 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 252 3 9 11 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 252
  (Polychromatic418967fa.accept_22_4_11_10_1_10691 26 33 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 33 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 33 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 252 3 8 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657
  23 33 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 22 33 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 252 3 7 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 252 (Polychromatic418967fa.accept_16_4_1_12_1_1792 20 33 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 252 (Polychromatic418967fa.accept_17_2_16_14_1_2116 19 33
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 252 3 6 11 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 252
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 33 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 252 (Polychromatic418967fa.accept_19_16_14_5_1_9920 16 33 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 252 3 5 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 252 (Polychromatic418967fa.accept_22_14_11_10_1_5824 14 33
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 13 33 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 252 3 4 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 33 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 252 (Polychromatic418967fa.accept_19_10_14_5_1_3079 10 33
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 252 3 3 11 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 252
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 33 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 33 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 252 3 2 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 33 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 252
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 4 33 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 252 3 1 11 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 33 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 33 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 252)))))))))))))))))))))))))))))))))
  (allB_succ 32 252 (allA_succ_of_accept 31 32 252 (accept_3_4 31 32 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 32 252 2 15 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 32 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 32 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 252 4 7 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 252 (Polychromatic418967fa.accept_13_1_6_5_1_1610
  27 32 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 252 2 13 16 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 252
  (accept_3_4 25 32 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 252 4 6 8 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 252
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 32 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 32 252 2 11 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 32 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 32 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 252 4 5 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 252 (accept_3_4 19 32 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 252 2 9 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 32 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 252 4 4 8 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 252
  (Polychromatic418967fa.accept_27_15_5_9_1_15189 15 32 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 32 252 2 7 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 32 252 (accept_3_4 13 32 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32
  252 4 3 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  32 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 32 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 32 252 2 5 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 32 252 (Polychromatic418967fa.accept_19_9_13_5_1_4351 9 32 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 252 4 2 8 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 252 (accept_3_4 7 32 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 252 2 3 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 32 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 252 4 1 8 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 252
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 32 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 252 2 1 16 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 252 (accept_3_4 1 32 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  252)))))))))))))))))))))))))))))))) (allB_succ 31 252 (allA_succ_of_accept 30 31 252
  (Polychromatic418967fa.accept_11_8_9_10_1_503 30 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 252 (accept_3_5 29 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 31 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 252 (accept_3_5 26 31 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 252 (Polychromatic418967fa.accept_26_25_5_18_1_15188 25 31 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 252
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 252 (accept_3_5 23 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 252 (Polychromatic418967fa.accept_25_22_6_2_1_15187 22 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 252 (Polychromatic418967fa.accept_20_1_11_12_1_2467 21 31 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 252 (accept_3_5 20 31 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 31 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 252
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 252 (accept_3_5 17 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 252 (Polychromatic418967fa.accept_19_15_12_5_1_8544 15 31 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 252 (accept_3_5 14 31 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 31 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 12 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 252 (accept_3_5 11 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 252 (Polychromatic418967fa.accept_25_10_6_2_1_15186 10 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 31 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 252 (accept_3_5 8 31 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 252 (Polychromatic418967fa.accept_19_7_12_5_1_7123 7 31 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 252 (accept_3_5 5 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  252 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 31 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 31 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 252 (accept_3_5 2 31 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 31 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 252))))))))))))))))))))))))))))))) (allB_succ 30 252
  (allA_succ_of_accept 29 30 252 (Polychromatic418967fa.accept_19_10_11_5_1_7093 29 30 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 252 2 14 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 252 3 9 10 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 252 2 13 15 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 252
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 30 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 30 252 6 4 5 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 30 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 252 2 11 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 30 252 3 7 10 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 30 252 2 10 15 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 30 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 252 6 3 5 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 252 (Polychromatic418967fa.accept_19_17_11_5_1_7092 17 30 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 252 2 8 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 252 3 5 10 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 252 2 7 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 252 (Polychromatic418967fa.accept_19_13_11_5_1_5692
  13 30 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 252 6 2 5 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 252
  (Polychromatic418967fa.accept_22_11_8_10_1_13740 11 30 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 252 2 5 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 252 3 3 10 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 252 2 4 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 30 252 (Polychromatic418967fa.accept_22_7_8_10_1_15185 7 30 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 252 6 1 5 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 252
  (Polychromatic418967fa.accept_20_5_10_12_1_8200 5 30 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 252 2 2 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 252 3 1 10 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 252 2 1 15 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 30 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 252)))))))))))))))))))))))))))))) (allB_succ 29 252 (allA_succ_of_accept
  28 29 252 (accept_3_4 28 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 29 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 252 (accept_3_4 25 29 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 29 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 252 (Polychromatic418967fa.accept_20_3_9_12_1_6671
  23 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 252 (accept_3_4 22
  29 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 21 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 252 (Polychromatic418967fa.accept_16_4_13_12_1_1740 20 29 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 252 (accept_3_4 19 29 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 252 (Polychromatic418967fa.accept_19_18_10_5_1_12639 18 29 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 252 (accept_3_4 16 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 29 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 252 (accept_3_4 13 29 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 252 (Polychromatic418967fa.accept_22_12_7_10_1_15184 12 29 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 252 (accept_3_4 10 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 29 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 252 (accept_3_4 7 29 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 252 (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 29 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 252
  (Polychromatic418967fa.accept_23_5_6_22_1_15183 5 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 252 (accept_3_4 4 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  252 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 29 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 29 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 29 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 252 (accept_3_4 1 29 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 29 252))))))))))))))))))))))))))))) (allB_succ 28 252 (allA_succ_of_accept 27 28 252
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 28 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 252 2 13 14 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 28 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 28 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 252 4 6 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 252 (accept_3_5 23 28 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 252 2 11 14 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 28 252 7 3 4 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 28 252 4 5 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 252 (Polychromatic418967fa.accept_24_19_4_12_1_6656 19 28
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 252 2 9 14 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 252 (accept_3_5 17
  28 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 252 4 4 7 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 28 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 28 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 252 14 1 2 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 252 (Polychromatic418967fa.accept_19_13_9_5_1_8541 13 28 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 252 4 3 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 252 (accept_3_5 11 28 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 28 252 2 5 14 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 28 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 28 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 252 4 2 7 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 28 252 7 1 4 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 28 252 2 3 14 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 252 (accept_3_5 5 28 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 252 4 1 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 28 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 252 2 1 14 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 252
  (Polychromatic418967fa.accept_15_1_13_12_1_347 1 28 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 252)))))))))))))))))))))))))))) (allB_succ 27 252 (allA_succ_of_accept 26 27 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 26 27 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 27 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 252 3 8 9 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 27 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 252
  (Polychromatic418967fa.accept_13_9_1_5_1_964 22 27 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 252 3 7 9 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 252 (Polychromatic418967fa.accept_16_4_11_12_1_1775 20 27 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 27 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 252 9 2 3 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 252
  (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 27 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 27 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 252 3 5 9 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 27 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 252
  (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 27 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 27 252 3 4 9 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 27 252 (Polychromatic418967fa.accept_30_11_27_12_1_15182 11 27 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 252
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 10 27 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 27 252 9 1 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 27 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176 8 27 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7
  27 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 252 3 2 9 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 27 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 27 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 252 3 1 9 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 252 (Polychromatic418967fa.accept_19_2_8_5_1_1885 2 27 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 252
  (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 27 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 252))))))))))))))))))))))))))) (allB_succ 26 252 (allA_succ_of_accept 25 26 252 (accept_3_4 25 26 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 252 2 12 13 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 252
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 26 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 252 2 11 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 26 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 26 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 252 2 10 13 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 252 (accept_3_4 19 26 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 252 2 9 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 252 (Polychromatic418967fa.accept_19_17_7_5_1_1883
  17 26 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 252 2 8 13 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 252
  (Polychromatic418967fa.accept_20_15_6_12_1_2446 15 26 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 252 2 7 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 252 (accept_3_4 13 26 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  252 2 6 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 26 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 252 2 5 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 26 252 (Polychromatic418967fa.accept_19_9_7_5_1_9887 9 26 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 252 2 4 13 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 252 (accept_3_4 7 26 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 252 2 3 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 26 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 252 2 2 13 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 252
  (Polychromatic418967fa.accept_16_3_10_12_1_4814 3 26 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 252 2 1 13 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 252 (accept_3_4 1 26 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  252)))))))))))))))))))))))))) (allB_succ 25 252 (allA_succ_of_accept 24 25 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 252 (accept_3_5 23 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 25 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 252 (accept_3_5 20 25 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 25 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 252 (accept_3_5 17 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 252 (Polychromatic418967fa.accept_17_16_8_14_1_6757 16 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 252 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 25 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 252 (accept_3_5 14 25 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 25 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 252
  (Polychromatic418967fa.accept_23_12_2_22_1_11999 12 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 25 252 (accept_3_5 11 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 25 252 (Polychromatic418967fa.accept_20_10_5_12_1_13866 10 25 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 25 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 252 (accept_3_5 8 25 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 7
  25 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 252 (accept_3_5 5 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  252 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 25 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 25 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 252 (accept_3_5 2 25 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 25 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 252))))))))))))))))))))))))) (allB_succ 24 252
  (allA_succ_of_accept 23 24 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 24 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 252 2 11 12 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 252 3 7 8 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 252 4 5 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 252 (Polychromatic418967fa.accept_13_6_11_5_1_133
  19 24 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 252 6 3 4 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 24 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 252 4 4 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 252 3 5 8 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 252 2 7 12 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 252 (Polychromatic418967fa.accept_16_13_8_12_1_2723 13 24 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 252 12 1 2 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 252 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 24
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 252 2 5 12 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 252 3 3 8 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 252 4 2 6 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 24 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 252 6 1 4 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 24 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 252 4 1 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 252 3 1 8 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 252 2 1 12 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 24 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 252)))))))))))))))))))))))) (allB_succ 23
  252 (allA_succ_of_accept 22 23 252 (accept_3_4 22 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 23 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 252 (accept_3_4 19 23 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 23 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 252 (accept_3_4 16 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 252 (Polychromatic418967fa.accept_22_14_1_10_1_5736 14 23 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 252 (accept_3_4 13 23 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 252 (Polychromatic418967fa.accept_19_12_4_5_1_9936 12 23
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 252 (accept_3_4 10 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 8 23 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 252 (accept_3_4 7 23 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 252 (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 23 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 252 (accept_3_4 4 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 23 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 2 23 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 252 (accept_3_4 1 23 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 252))))))))))))))))))))))) (allB_succ 22 252 (allA_succ_of_accept 21 22 252
  (Polychromatic418967fa.accept_15_6_7_12_1_869 21 22 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 252 2 10 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 22 252 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 22 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 252 2 9 11 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 252 (accept_3_5 17 22 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 252 2 8 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 22 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 15
  22 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 252 2 7 11 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 252
  (Polychromatic418967fa.accept_25_13_22_2_1_15181 13 22 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 22 252 2 6 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 22 252 (accept_3_5 11 22 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 22 252 2 5 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 22 252 (Polychromatic418967fa.accept_17_9_5_14_1_4277 9 22 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 252 2 4 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 252 (Polychromatic418967fa.accept_19_7_3_5_1_8585 7 22 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 252 2 3 11 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 252 (accept_3_5 5 22 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 252 2 2 11 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3
  22 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 252 2 1 11 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 252
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 22 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 252)))))))))))))))))))))) (allB_succ 21 252 (allA_succ_of_accept 20 21 252
  (Polychromatic418967fa.accept_15_5_6_12_1_916 20 21 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 21 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 252 3 6 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 21 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 16 21 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 252 3 5 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 21 252 7 2 3 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 21 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 21 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 252 3 4 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 252 (Polychromatic418967fa.accept_20_11_1_12_1_3803 11 21
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 252
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 21 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 21 252 3 3 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 21 252 (Polychromatic418967fa.accept_16_8_5_12_1_3812 8 21 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 252 7 1 3 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 21 252 3 2 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 21 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 252
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 4 21 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 252 3 1 7 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 21 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 21 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 252))))))))))))))))))))) (allB_succ 20 252
  (allA_succ_of_accept 19 20 252 (accept_3_4 19 20 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20
  252 2 9 10 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  20 252 (Polychromatic418967fa.accept_15_2_5_12_1_369 17 20 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 252 4 4 5 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 20 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 20 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 252 2 7 10 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 252 (accept_3_4 13 20 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 252 4 3 5 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 20 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 252 2 5 10 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 252
  (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 20 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 252 4 2 5 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 252 (accept_3_4 7 20 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 252
  2 3 10 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  252 (Polychromatic418967fa.accept_16_5_4_12_1_3800 5 20 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 20 252 4 1 5 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 20 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 20 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 252 2 1 10 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 252 (accept_3_4 1 20 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 20 252)))))))))))))))))))) (allB_succ 19 252 (allA_succ_of_accept 18 19 252
  (Polychromatic418967fa.accept_23_18_19_22_1_15180 18 19 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 252 (accept_3_5 17 19 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 16 19 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 19 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 252 (accept_3_5 14 19 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 252
  (Polychromatic418967fa.accept_20_13_19_12_1_5143 13 19 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 19 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 19 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 252 (accept_3_5 11 19 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 252 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 19
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 252
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 19 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 252 (accept_3_5 8 19 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 19 252 (Polychromatic418967fa.accept_24_6_19_12_1_11904 6 19 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 252 (accept_3_5 5 19 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 19 252 (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 19 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3
  19 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 252 (accept_3_5 2 19 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 1
  19 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 252))))))))))))))))))) (allB_succ 18
  252 (allA_succ_of_accept 17 18 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 18 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 252 2 8 9 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 18 252 3 5 6 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 18 252 2 7 9 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 252 (Polychromatic418967fa.accept_15_13_3_12_1_1609
  13 18 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 252 6 2 3 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 252
  (Polychromatic418967fa.accept_22_11_18_10_1_12179 11 18 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 252 2 5 9 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 18 252 9 1 2 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 18 252 2 4 9 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 18 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 18 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 252 6 1 3 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5
  18 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 252 2 2 9 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 252 3 1 6 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 252 2 1 9 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 252
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 1 18 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 252)))))))))))))))))) (allB_succ 17 252 (allA_succ_of_accept 16 17 252 (accept_3_4 16 17 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 17 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 17 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 252 (accept_3_4 13 17 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 17 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 252 (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 17 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 252 (accept_3_4 10 17 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 17 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 252
  (Polychromatic418967fa.accept_16_8_1_12_1_984 8 17 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 252 (accept_3_4 7 17 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  252 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 17 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 252 (accept_3_4 4 17 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 17 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 252
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 17 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 252 (accept_3_4 1 17 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  252))))))))))))))))) (allB_succ 16 252 (allA_succ_of_accept 15 16 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 15
  16 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 16 252 2 7 8 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 16 252
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 16 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 16 252 4 3 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 16 252 (accept_3_5 11 16 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16
  252 2 5 8 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  16 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 16 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 16 252 4 2 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 16 252 (Polychromatic418967fa.accept_22_7_16_10_1_7361 7 16 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 252 2 3 8 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 252 (accept_3_5 5 16 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 252 4 1 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 16 252 (Polychromatic418967fa.accept_19_3_16_5_1_7098 3 16 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 16 252 2 1 8 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 16 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 16 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 252)))))))))))))))) (allB_succ 15 252 (allA_succ_of_accept 14 15 252
  (Polychromatic418967fa.accept_22_14_15_10_1_12213 14 15 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 15 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 15 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 252 3 4 5 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 11
  15 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 252
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 15 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 252 3 3 5 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 15 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 15 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 252 3 2 5 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 15 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 15 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 252 3 1 5 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 252 (Polychromatic418967fa.accept_16_2_15_12_1_1744 2 15 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 252
  (Polychromatic418967fa.accept_19_1_15_5_1_4357 1 15 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 252))))))))))))))) (allB_succ 14 252 (allA_succ_of_accept 13 14 252 (accept_3_4 13 14 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 252 2 6 7 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 252 (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 14
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 252 2 5 7 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 252
  (Polychromatic418967fa.accept_13_9_1_5_1_964 9 14 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 252 2 4 7 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 14 252 7 1 2 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 14 252 2 3 7 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 14 252 (Polychromatic418967fa.accept_23_5_14_22_1_15179 5 14 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 252 2 2 7 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 14 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 252 2 1 7 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 252 (accept_3_4 1 14 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 252)))))))))))))) (allB_succ 13 252 (allA_succ_of_accept 12 13
  252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 13 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 252 (accept_3_5 11 13 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 252 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 13 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 13 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 252 (accept_3_5 8 13 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 252 (Polychromatic418967fa.accept_19_7_13_5_1_7125
  7 13 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 252
  (Polychromatic418967fa.accept_24_6_13_12_1_15178 6 13 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 252 (accept_3_5 5 13 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  252 (Polychromatic418967fa.accept_16_4_13_12_1_1740 4 13 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 13 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 252 (accept_3_5 2 13 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 13 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 252))))))))))))) (allB_succ 12 252
  (allA_succ_of_accept 11 12 252 (Polychromatic418967fa.accept_17_11_12_14_1_5431 11 12 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 252 2 5 6 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 12 252 3 3 4 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 12 252 4 2 3 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 12 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 252 6 1 2 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 252
  (Polychromatic418967fa.accept_26_5_12_18_1_15177 5 12 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 252 4 1 3 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 12 252 3 1 4 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 12 252 2 1 6 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 12 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 252)))))))))))) (allB_succ 11 252 (allA_succ_of_accept 10 11 252
  (accept_3_4 10 11 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 9 11 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 252 (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 11 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 252 (accept_3_4 7 11 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 11 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 252
  (Polychromatic418967fa.accept_26_5_11_18_1_15176 5 11 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 252 (accept_3_4 4 11 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11
  252 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 11 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 11 252 (Polychromatic418967fa.accept_23_2_11_22_1_15175 2 11 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 252 (accept_3_4 1 11 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 11 252))))))))))) (allB_succ 10 252 (allA_succ_of_accept 9 10 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 10 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 252 2 4 5 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 10 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 252 2 3 5 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 252 (accept_3_5 5 10 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 252 2 2 5 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 252 (Polychromatic418967fa.accept_16_3_10_12_1_4814 3 10 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 252 2 1 5 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 252 (Polychromatic418967fa.accept_17_1_10_14_1_1173
  1 10 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 252)))))))))) (allB_succ 9 252
  (allA_succ_of_accept 8 9 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 9 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 9 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 252 3 2 3 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 9 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 9 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 252 3 1 3 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 2 9 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 1 9 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 252))))))))) (allB_succ 8 252 (allA_succ_of_accept 7 8 252 (accept_3_4 7 8 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 252 2 3 4 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 8 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 8 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 252 4 1 2 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 252
  (Polychromatic418967fa.accept_13_3_8_5_1_974 3 8 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 252 2 1 4 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 252 (accept_3_4 1 8 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 252))))))))
  (allB_succ 7 252 (allA_succ_of_accept 6 7 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 6 7 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 7 252 (accept_3_5 5 7 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 7 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 7 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 7 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 7 252 (accept_3_5 2 7 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 7 252
  (Polychromatic418967fa.accept_23_1_7_22_1_12002 1 7 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 7 252))))))) (allB_succ 6 252 (allA_succ_of_accept 5 6 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5
  6 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 252 2 2 3 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 6 252 3 1 2 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 6 252 2 1 3 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 6 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 252)))))) (allB_succ 5 252 (allA_succ_of_accept 4 5 252 (accept_3_4 4 5 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 5 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 252 (Polychromatic418967fa.accept_15_2_5_12_1_369 2
  5 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 252 (accept_3_4 1 5 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 252))))) (allB_succ 4 252 (allA_succ_of_accept 3 4 252
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 4 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 252 2 1 2 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 4 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 4 252)))) (allB_succ 3 252 (allA_succ_of_accept 2 3 252
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 3 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 3 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 252))) (allB_succ 2 252 (allA_succ_of_accept 1 2 252 (accept_3_4 1 2 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 252)) (allB_two
  252)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


