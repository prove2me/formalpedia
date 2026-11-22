-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch248_Segment000
-- name    : Polychromatic418967fa_Branch248_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:39:55.331319+00:00
-- url     : https://prove2.me/theorems/1f1ee3cc-0ff4-4b10-8248-71d558d22cea
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

def Polychromatic418967fa.branch_248_segment_000 : allB 123 248 :=
  allB_succ 122 248 (allA_succ_of_accept 121 122 248 (accept_3_2 121 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 122 248 2 60 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 122 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 119 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 122 248 2 59 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 122 248
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 117 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 122 248 2 58 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 122 248 (accept_3_2 115 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 122 248 2 57 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 122 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 113 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 122 248 2 56 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 122 248
  (Polychromatic418967fa.accept_15_6_2_8_1_2223 111 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 122 248 2 55 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 122 248 (accept_3_2 109 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 122 248 2 54 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 122 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 107 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 248 2 53 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 105 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 248 2 52 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 248 (accept_3_2 103 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 248 2 51 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 101 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 248 2 50 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 248
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 99 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 248 2 49 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 248 (accept_3_2 97 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 248 2 48 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 95 122 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 248 2 47 61 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 248
  (Polychromatic418967fa.accept_11_5_1_6_1_774 93 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 248 2 46 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 248 (accept_3_2 91 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 248 2 45 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 122 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 248 2 44 61 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 248
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 87 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 248 2 43 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 248 (accept_3_2 85 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 248 2 42 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 248 2 41 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 248
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 81 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 248 2 40 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 248 (accept_3_2 79 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 248 2 39 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 122 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 248 2 38 61 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 75 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 248 2 37 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 248 (accept_3_2 73 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 248 2 36 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 248 (Polychromatic418967fa.accept_11_5_1_6_1_774 71 122 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 248 2 35 61 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 248
  (Polychromatic418967fa.accept_13_4_5_1_1_833 69 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 248 2 34 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 248 (accept_3_2 67 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 248 2 33 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 122 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 248 2 32 61 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 248
  (Polychromatic418967fa.accept_22_19_12_6_1_2480 63 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 122 248 2 31 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 122 248 (accept_3_2 61 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 248 2 30 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 248 2 29 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 248
  (Polychromatic418967fa.accept_23_11_7_18_1_13430 57 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 122 248 2 28 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 122 248 (accept_3_2 55 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 248 2 27 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 122 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 248 2 26 61 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 248
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 51 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 248 2 25 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 248 (accept_3_2 49 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 248 2 24 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 248 2 23 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 248 2 22 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 248 (accept_3_2 43 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 248 2 21 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 122 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 248 2 20 61 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 248
  (Polychromatic418967fa.accept_15_9_2_8_1_1379 39 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 248 2 19 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 248 (accept_3_2 37 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 248 2 18 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 122 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 248 2 17 61 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 248
  (Polychromatic418967fa.accept_25_8_22_23_1_11506 33 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 122 248 2 16 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 122 248 (accept_3_2 31 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 248 2 15 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 248 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 248 2 14 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 248
  (Polychromatic418967fa.accept_11_5_1_6_1_774 27 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 248 2 13 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 248 (accept_3_2 25 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 248 2 12 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 248 2 11 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 248
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 248 2 10 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 248 (accept_3_2 19 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 248 2 9 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 122 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 248 2 8 61 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 248 2 7 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 248 (accept_3_2 13 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 248 2 6 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 248 2 5 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 248
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 248 2 4 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 248 (accept_3_2 7 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  248 2 3 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 122 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 248 2 2 61 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 248 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 122 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 248 2 1 61 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 248 (accept_3_2 1 122 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 248 (allA_of_3_0 121 121 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 248
  (allA_succ_of_accept 119 120 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 119 120 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 120 248 2 59 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 120 248 (Polychromatic418967fa.accept_7_5_1_3_1_103
  117 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 120 248 4 29 30 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 120 248
  (accept_3_2 115 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 120 248 2 57 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 120 248
  (Polychromatic418967fa.accept_17_11_1_10_1_3925 113 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 112 120 248 8 14 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 111 120 248 (Polychromatic418967fa.accept_13_7_3_1_1_814 111 120 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 120 248 2 55 60 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 248 (accept_3_2 109 120 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 120 248 4 27 30 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 120 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 107 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 120 248 2 53 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 120 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 120 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 120 248 8 13 15 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 248 (accept_3_2 103 120 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 120 248 2 51 60 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 120 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 101 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 248 4 25 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 120 248 (Polychromatic418967fa.accept_17_14_1_10_1_3941 99 120 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 120 248 2 49 60 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 248 (accept_3_2 97 120 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 120 248 8 12 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 120 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 95 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 120 248 2 47 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 120 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 93 120 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 248 4 23 30 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 248 (accept_3_2 91 120 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 120 248 2 45 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 120 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 89
  120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 248 8 11 15 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 120 248
  (Polychromatic418967fa.accept_9_6_3_5_1_240 87 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 120 248 2 43 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 120 248 (accept_3_2 85 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 248 4 21 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 120 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 248 2 41 60 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 120 248 8 10 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 120 248 (accept_3_2 79 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 248 2 39 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 248 (Polychromatic418967fa.accept_17_9_1_10_1_2859 77 120 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 248 4 19 30 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 120 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 120 248 2 37 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 120 248 (accept_3_2 73 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 248 8 9 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 120 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 120 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 248 2 35 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 69
  120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 248 4 17 30 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 248 (accept_3_2 67
  120 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 248 2 33 60 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 120 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 120 248 8 8 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 120 248 (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 120 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 120 248 2 31 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 248 (accept_3_2 61 120 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 248 4 15 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 248 (Polychromatic418967fa.accept_13_7_3_1_1_814 59 120 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 248 2 29 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 248
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 57 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 248 8 7 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 120 248 (accept_3_2 55 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  120 248 2 27 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 120 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 120 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 248 4 13 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 51
  120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 248 2 25 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 248 (accept_3_2 49
  120 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 248 8 6 15 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 248 2 23 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 120 248 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 120 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 120 248 4 11 30 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 248 (accept_3_2 43 120 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 248 2 21 60 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 248
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 248 8 5 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 120 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 120 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 248 2 19 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 248 (accept_3_2 37 120 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 248 4 9 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 120 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 120 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 248 2 17 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 248 8 4 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 120 248 (accept_3_2 31 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  120 248 2 15 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 248 4 7 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 248 (Polychromatic418967fa.accept_11_5_10_6_1_793
  27 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 248 2 13 60 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 248
  (accept_3_2 25 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 248 8 3 15 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 248 2 11 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 120 248 (Polychromatic418967fa.accept_18_3_12_14_1_2232 21 120 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 248 4 5 30 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 248 (accept_3_2 19 120 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 248 2 9 60 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 248
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 248 8 2 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 120 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 120 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 248 2 7 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 248 (accept_3_2 13 120 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 248 4 3 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 120 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 248 2 5 60 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 248 8 1 15 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 248 (accept_3_2 7 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120
  248 2 3 60 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  120 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 120 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 248 4 1 30 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 120 248 (Polychromatic418967fa.accept_18_3_12_14_1_2232 3 120 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 248 2 1 60 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 248 (accept_3_2 1 120 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 248 (allA_succ_of_accept 118 119 248 (accept_3_2 118 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 119 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 116 119
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 248 (accept_3_2 115 119
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 114 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 248 (Polychromatic418967fa.accept_11_3_9_6_1_105 113 119 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 248 (accept_3_2 112 119 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 248
  (Polychromatic418967fa.accept_12_2_11_8_1_504 110 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 248 (accept_3_2 109 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 248 (Polychromatic418967fa.accept_16_12_7_8_1_1589 108 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 107 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 248 (accept_3_2 106 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 119
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 248
  (Polychromatic418967fa.accept_10_4_9_8_1_125 104 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 119 248 (accept_3_2 103 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 119 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 119 248 (Polychromatic418967fa.accept_10_1_9_8_1_123 101 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 248 (accept_3_2 100 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 98 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 248 (accept_3_2 97 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 248 (Polychromatic418967fa.accept_14_11_7_10_1_4852 95 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 248 (accept_3_2 94 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 248
  (Polychromatic418967fa.accept_16_12_7_8_1_1589 92 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 248 (accept_3_2 91 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 248 (Polychromatic418967fa.accept_13_12_2_1_1_2909 90 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 248 (accept_3_2 88 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 248
  (Polychromatic418967fa.accept_12_2_11_8_1_504 86 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 119 248 (accept_3_2 85 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 119 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 119 248 (Polychromatic418967fa.accept_21_20_14_17_1_10643 83 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 248 (accept_3_2 82 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 119 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 80 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 119 248 (accept_3_2 79 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 119 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 119 248 (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 248 (accept_3_2 76 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 248
  (Polychromatic418967fa.accept_10_4_9_8_1_125 74 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 119 248 (accept_3_2 73 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 119 248 (Polychromatic418967fa.accept_19_15_5_1_1_5360 72 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 248 (accept_3_2 70 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 248
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 68 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 248 (accept_3_2 67 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 248 (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 248 (accept_3_2 64 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 248 (accept_3_2 61 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 248 (Polychromatic418967fa.accept_14_3_7_10_1_2146 59 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 248 (accept_3_2 58 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 248
  (Polychromatic418967fa.accept_18_2_11_14_1_69 56 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 248 (accept_3_2 55 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 248 (accept_3_2 52 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 248
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 248 (accept_3_2 49 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 248 (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 248 (accept_3_2 46 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 248 (accept_3_2 43 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 248 (Polychromatic418967fa.accept_10_1_9_8_1_123 41 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 248 (accept_3_2 40 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 248
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 248 (accept_3_2 37 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 248 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 248 (accept_3_2 34 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 248
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 248 (accept_3_2 31 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 248 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 248 (accept_3_2 28 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 248 (accept_3_2 25 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 248 (Polychromatic418967fa.accept_18_5_11_14_1_7203 23 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 248 (accept_3_2 22 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 248
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 248 (accept_3_2 19 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 248 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 248 (accept_3_2 16 119 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 248
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 248 (accept_3_2 13 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 248 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 248 (accept_3_2 10 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 248 (accept_3_2 7 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 248 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 248 (accept_3_2 4 119 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 248
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 248 (accept_3_2 1 119 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 248 (allA_of_3_0 118 118 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 248
  (allA_succ_of_accept 116 117 248 (Polychromatic418967fa.accept_15_11_12_8_1_739 116 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 248 (accept_3_2 115 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 114 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 248 (accept_3_2 112 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 248 (Polychromatic418967fa.accept_11_1_7_6_1_378 111 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 248 (Polychromatic418967fa.accept_14_12_5_10_1_2130 110 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 248 (accept_3_2 109 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 248 (Polychromatic418967fa.accept_15_3_12_8_1_738 108 117
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 248 (accept_3_2 106 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 105 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 117 248 (Polychromatic418967fa.accept_17_2_15_10_1_5171 104 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 248 (accept_3_2 103 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 102 117
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 117 248 (accept_3_2 100 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 117 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 99 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 117 248 (Polychromatic418967fa.accept_27_17_9_5_1_7237 98 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 248 (accept_3_2 97 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 248 (Polychromatic418967fa.accept_14_12_5_10_1_2130 96 117
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 248 (accept_3_2 94 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 92 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 248 (accept_3_2 91 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 248 (accept_3_2 88 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 117 248 (Polychromatic418967fa.accept_17_2_15_10_1_5171 87 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 117 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 248 (accept_3_2 85 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 248 (Polychromatic418967fa.accept_16_4_5_8_1_2425 84 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 248 (accept_3_2 82 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 117 248 (Polychromatic418967fa.accept_19_5_3_1_1_4055 81 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 248 (Polychromatic418967fa.accept_15_5_12_8_1_3168 80 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 248 (accept_3_2 79 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 117 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 248 (accept_3_2 76 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 75 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 248 (Polychromatic418967fa.accept_19_17_3_1_1_4056 74 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 248 (accept_3_2 73 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 117 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 248 (accept_3_2 70 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 248 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 248 (Polychromatic418967fa.accept_14_12_5_10_1_2130 68 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 248 (accept_3_2 67 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 117
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 248 (accept_3_2 64 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 248 (Polychromatic418967fa.accept_15_3_12_8_1_738 63 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 248 (Polychromatic418967fa.accept_19_5_3_1_1_4055 62 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 248 (accept_3_2 61 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 248 (Polychromatic418967fa.accept_16_12_5_8_1_2492 60 117
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 248 (accept_3_2 58 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 248 (Polychromatic418967fa.accept_11_1_7_6_1_378 56 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 248 (accept_3_2 55 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 117
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 248 (accept_3_2 52 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 248 (accept_3_2 49 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 248 (Polychromatic418967fa.accept_15_3_12_8_1_738 48 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 248 (accept_3_2 46 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 248 (accept_3_2 43 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 248 (accept_3_2 40 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 248 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 248 (Polychromatic418967fa.accept_17_4_15_10_1_5139 38 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 248 (accept_3_2 37 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 117 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 248 (accept_3_2 34 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 248 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 248 (Polychromatic418967fa.accept_28_4_5_24_1_15011 32 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 248 (accept_3_2 31 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 117 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 248 (accept_3_2 28 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 248 (Polychromatic418967fa.accept_16_11_5_8_1_2427 27 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 248 (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 248 (accept_3_2 25 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 248 (Polychromatic418967fa.accept_18_6_9_14_1_9915 24 117
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 248 (accept_3_2 22 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 248 (Polychromatic418967fa.accept_17_4_15_10_1_5139 21 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 248 (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 248 (accept_3_2 19 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 117
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 248 (accept_3_2 16 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 248 (Polychromatic418967fa.accept_24_14_21_8_1_4565 14 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 248 (accept_3_2 13 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 248 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 117
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 248 (accept_3_2 10 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 248 (accept_3_2 7 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 117 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 248 (accept_3_2 4 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 248 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 117 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 248 (accept_3_2 1 117 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 248 (allA_succ_of_accept 115 116 248 (accept_3_2 115 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 248 2 57 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 113 116 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 248 4 28 29 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 111 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 116 248 2 55 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 116 248 (accept_3_2 109 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 248 4 27 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 248 (Polychromatic418967fa.accept_16_11_4_8_1_3435 107 116 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 248 2 53 58 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 248
  (Polychromatic418967fa.accept_9_6_8_5_1_837 105 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 116 248 4 26 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 116 248 (accept_3_2 103 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 248 2 51 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 101 116 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 248 4 25 29 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 99 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 248 2 49 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 248 (accept_3_2 97 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 248 4 24 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 248 (Polychromatic418967fa.accept_15_5_11_8_1_1391 95 116 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 248 2 47 58 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 93 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 248 4 23 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 248 (accept_3_2 91 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 248 2 45 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 248 (Polychromatic418967fa.accept_13_11_12_1_1_2154 89 116 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 248 4 22 29 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 248
  (Polychromatic418967fa.accept_9_6_8_5_1_837 87 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 248 2 43 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 248 (accept_3_2 85 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 248 4 21 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 116 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 248 2 41 58 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 248
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 81 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 248 4 20 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 248 (accept_3_2 79 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 248 2 39 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 248 (Polychromatic418967fa.accept_14_7_4_10_1_1351 77 116 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 248 4 19 29 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 248 2 37 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 248 (accept_3_2 73 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 248 4 18 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 116 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 248 2 35 58 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 248 4 17 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 248 (accept_3_2 67 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 248 2 33 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 116 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 248 4 16 29 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 248
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 116 248 2 31 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 116 248 (accept_3_2 61 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 248 4 15 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 248 (Polychromatic418967fa.accept_16_11_4_8_1_3435 59 116 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 248 2 29 58 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 248 4 14 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 248 (accept_3_2 55 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 248 2 27 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 116 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 248 4 13 29 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 248
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 248 2 25 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 248 (accept_3_2 49 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 248 4 12 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 116 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 248 2 23 58 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 248
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 248 4 11 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 248 (accept_3_2 43 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 248 2 21 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 116 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 248 4 10 29 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 248 2 19 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 248 (accept_3_2 37 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 248 4 9 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 248 (Polychromatic418967fa.accept_14_7_4_10_1_1351 35 116 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 248 2 17 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 33
  116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 248 4 8 29 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 248 (accept_3_2 31
  116 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 248 2 15 58 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 248 4 7 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 116 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 248 2 13 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 248 (accept_3_2 25 116 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 248 4 6 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 116
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 248 2 11 58 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 248 4 5 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 248 (accept_3_2 19 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 248 2 9 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 248 (Polychromatic418967fa.accept_16_1_4_8_1_3434 17 116 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 248 4 4 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 248 2 7 58 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 248 (accept_3_2 13
  116 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 248 4 3 29 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 248 2 5 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 116 248 (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 116 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 248 4 2 29 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 248 (accept_3_2 7 116 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 248 2 3 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 248 (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 116 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 248 4 1 29 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 248 2 1 58 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 248 (accept_3_2 1 116 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 248 (allA_of_3_0 115 115 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 248
  (allA_succ_of_accept 113 114 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 113 114 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 248 2 56 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 114 248 (Polychromatic418967fa.accept_7_6_2_3_1_107
  111 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 248 2 55 57 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 248
  (accept_3_2 109 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 114 248 2 54 57 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 114 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 107 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 248 2 53 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 248 (Polychromatic418967fa.accept_12_9_6_8_1_518 105 114 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 248 2 52 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 248 (accept_3_2 103 114 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 114 248 2 51 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 114 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 101 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 248 2 50 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 99 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 248 2 49 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 248 (accept_3_2 97 114 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 248 2 48 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 248 (Polychromatic418967fa.accept_13_4_10_1_1_1390
  95 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 248 2 47 57 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 93 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 114 248 2 46 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 114 248 (accept_3_2 91 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 248 2 45 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 248 2 44 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 248 2 43 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 248 (accept_3_2 85 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 248 2 42 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 248 2 41 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 248 2 40 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 248 (accept_3_2 79 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 248 2 39 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 248 (Polychromatic418967fa.accept_15_2_9_8_1_736 77 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 248 2 38 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 248 2 37 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 248 (accept_3_2 73 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 248 2 36 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 248 2 35 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 248 2 34 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 248 (accept_3_2 67 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 248 2 33 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 248 2 32 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 248 2 31 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 248 (accept_3_2 61 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 248 2 30 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 248 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 248 2 29 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 248 2 28 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 248 (accept_3_2 55 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 248 2 27 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 248 2 26 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 248 2 25 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 248 (accept_3_2 49 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 248 2 24 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 248 2 23 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 248 2 22 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 248 (accept_3_2 43 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 248 2 21 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 248 2 20 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 248 2 19 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 248 (accept_3_2 37 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 248 2 18 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 248 2 17 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 248 2 16 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 248 (accept_3_2 31 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 248 2 15 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 248 2 14 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 248 2 13 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 248 (accept_3_2 25 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 248 2 12 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 248 (Polychromatic418967fa.accept_17_6_12_10_1_7781 23 114 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 248 2 11 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 248 2 10 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 248 (accept_3_2 19 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 248 2 9 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 248 2 8 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 248 2 7 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 248 (accept_3_2 13 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 248 2 6 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 114 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 248 2 5 57 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 248
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 248 2 4 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 248 (accept_3_2 7 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  248 2 3 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 114 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 248 2 2 57 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 114 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 248 2 1 57 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 248 (accept_3_2 1 114 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 248 (allA_succ_of_accept 112 113 248 (accept_3_2 112 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 110 113
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 248 (accept_3_2 109 113
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 248
  (Polychromatic418967fa.accept_11_9_3_6_1_797 108 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 107 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 248 (accept_3_2 106 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 248
  (Polychromatic418967fa.accept_21_20_8_17_1_7437 104 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 113 248 (accept_3_2 103 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 113 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 102 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 113 248 (Polychromatic418967fa.accept_10_1_3_8_1_136 101 113
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 248 (accept_3_2 100 113
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 99 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 113 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 98 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 113 248 (accept_3_2 97 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 113 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 113 248 (Polychromatic418967fa.accept_7_4_1_3_1_277
  95 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 248 (accept_3_2 94
  113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 113 248 (Polychromatic418967fa.accept_16_12_1_8_1_5767 92 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 113 248 (accept_3_2 91 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 113 248 (Polychromatic418967fa.accept_19_14_18_1_1_12442 90 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 89 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 113 248 (accept_3_2 88 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 113 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 86 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 113 248 (accept_3_2 85 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 113 248 (Polychromatic418967fa.accept_13_6_9_1_1_5604 84 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 248
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 83 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 113 248 (accept_3_2 82 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 113 248 (Polychromatic418967fa.accept_13_2_9_1_1_67 80 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 113 248 (accept_3_2 79 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 113 248 (Polychromatic418967fa.accept_19_2_18_1_1_8275 78 113 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 248
  (Polychromatic418967fa.accept_21_14_8_17_1_15010 77 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 113 248 (accept_3_2 76 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 74 113 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 248 (accept_3_2 73 113 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 113 248 (Polychromatic418967fa.accept_7_2_1_3_1_102
  72 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 248
  (Polychromatic418967fa.accept_10_1_3_8_1_136 71 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 113 248 (accept_3_2 70 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 113 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 248 (accept_3_2 67 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 66 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 248 (accept_3_2 64 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 248 (accept_3_2 61 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 113 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 248
  (Polychromatic418967fa.accept_19_2_18_1_1_8275 59 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 248 (accept_3_2 58 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 248 (accept_3_2 55 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 113 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 248 (accept_3_2 52 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 248 (accept_3_2 49 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 248 (Polychromatic418967fa.accept_28_20_1_24_1_13035 48
  113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 248 (accept_3_2 46 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 248 (accept_3_2 43 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 248 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 248
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 248 (accept_3_2 40 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 248 (accept_3_2 37 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 113
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 248
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 248 (accept_3_2 34 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 248 (accept_3_2 31 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 248
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 29 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 113 248 (accept_3_2 28 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 113 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 248 (accept_3_2 25 113 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 248
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 113 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 248 (accept_3_2 22 113 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 248 (Polychromatic418967fa.accept_11_9_3_6_1_797
  20 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 248 (accept_3_2 19
  113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 113 248 (Polychromatic418967fa.accept_19_17_18_1_1_3980 17 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 248 (accept_3_2 16 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 248
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 248 (accept_3_2 13 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 248 (accept_3_2 10 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 248
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 248 (accept_3_2 7 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 248 (accept_3_2 4 113 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 248 (accept_3_2 1 113 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 248 (allA_of_3_0 112 112 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 248
  (allA_succ_of_accept 110 111 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 110 111 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 248 (accept_3_2 109 111 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 248 (Polychromatic418967fa.accept_16_12_15_8_1_4586 108 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 248 (accept_3_2 106 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 248 (Polychromatic418967fa.accept_11_5_1_6_1_774 104 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 248 (accept_3_2 103 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 111
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 248 (accept_3_2 100 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 248 (Polychromatic418967fa.accept_10_9_1_8_1_755 99 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 248 (accept_3_2 97 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 248 (accept_3_2 94 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 92 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 248 (accept_3_2 91 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 248 (accept_3_2 88 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 86 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 248 (accept_3_2 85 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 248 (Polychromatic418967fa.accept_11_7_1_6_1_1281 84 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 248 (accept_3_2 82 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 80 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 248 (accept_3_2 79 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 248 (accept_3_2 76 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 248 (Polychromatic418967fa.accept_21_12_6_17_1_12037 75 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 248 (accept_3_2 73 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 111 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 248 (accept_3_2 70 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 248 (Polychromatic418967fa.accept_13_3_7_1_1_334 68 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 248 (accept_3_2 67 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 111
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 248 (accept_3_2 64 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 248 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 248 (accept_3_2 61 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 248 (accept_3_2 58 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 248 (Polychromatic418967fa.accept_16_9_15_8_1_3425 57 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 248 (accept_3_2 55 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 248 (accept_3_2 52 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 248 (Polychromatic418967fa.accept_13_11_7_1_1_1386 50 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 248 (accept_3_2 49 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 248 (Polychromatic418967fa.accept_18_12_3_14_1_5919 48 111
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 248 (accept_3_2 46 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 248 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 248 (accept_3_2 43 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 248 (accept_3_2 40 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 248 (accept_3_2 37 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 248 (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 111 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 248 (accept_3_2 34 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 248 (accept_3_2 31 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 248 (accept_3_2 28 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 248 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 248 (accept_3_2 25 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 248 (accept_3_2 22 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 248 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 248 (accept_3_2 19 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 248 (accept_3_2 16 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 248 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 248 (accept_3_2 13 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 248 (Polychromatic418967fa.accept_16_12_15_8_1_4586 12 111
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 248 (accept_3_2 10 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 248 (accept_3_2 7 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 248 (accept_3_2 4 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 248 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 111 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 248 (accept_3_2 1 111 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 248 (allA_succ_of_accept 109 110 248 (accept_3_2 109 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 248 2 54 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 107 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 248 2 53 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 110 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 105 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 110 248 2 52 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 110 248 (accept_3_2 103 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 110 248 2 51 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 110 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 101 110 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 248 2 50 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 99 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 110 248 2 49 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 110 248 (accept_3_2 97 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 248 2 48 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 110 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 248 2 47 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 248 2 46 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 248 (accept_3_2 91 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 248 2 45 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 248 2 44 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 87 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 248 2 43 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 248 (accept_3_2 85 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 248 2 42 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 110 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 248 2 41 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 248
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 81 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 248 2 40 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 248 (accept_3_2 79 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 248 2 39 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 248 2 38 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 75 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 248 2 37 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 248 (accept_3_2 73 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 248 2 36 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 248 2 35 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 69 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 248 2 34 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 248 (accept_3_2 67 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 248 2 33 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 248 2 32 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 248
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 248 2 31 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 248 (accept_3_2 61 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 248 2 30 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 110 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 248 2 29 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 248 2 28 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 248 (accept_3_2 55 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 248 2 27 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 248 2 26 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 248 2 25 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 248 (accept_3_2 49 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 248 2 24 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 110 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 248 2 23 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 248
  (Polychromatic418967fa.accept_20_5_10_8_1_6397 45 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 248 2 22 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 248 (accept_3_2 43 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 248 2 21 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 248 2 20 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 248 2 19 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 248 (accept_3_2 37 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 248 2 18 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 248 2 17 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 248 2 16 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 248 (accept_3_2 31 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 248 2 15 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 248 2 14 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 248
  (Polychromatic418967fa.accept_15_12_5_8_1_5247 27 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 248 2 13 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 248 (accept_3_2 25 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 248 2 12 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 248 2 11 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 248 2 10 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 248 (accept_3_2 19 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 248 2 9 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 110 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 248 2 8 55 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 110 248 2 7 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 110 248 (accept_3_2 13 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 248 2 6 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 110 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 248 2 5 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 248 2 4 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 248 (accept_3_2 7 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  248 2 3 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 110 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 248 2 2 55 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 110 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 248 2 1 55 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 248 (accept_3_2 1 110 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 248 (allA_of_3_0 109 109 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 248
  (allA_succ_of_accept 107 108 248 (Polychromatic418967fa.accept_13_3_4_1_1_363 107 108 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 248 2 53 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 248
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 105 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 108 248 4 26 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 108 248 (accept_3_2 103 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 248 2 51 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 248 (Polychromatic418967fa.accept_13_10_4_1_1_2142 101 108 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 248 4 25 27 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 108 248
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 99 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 108 248 2 49 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 108 248 (accept_3_2 97 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 248 4 24 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 248 (Polychromatic418967fa.accept_15_5_3_8_1_748 95 108 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 248 2 47 54 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 108 248
  (Polychromatic418967fa.accept_16_13_12_8_1_2451 93 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 108 248 4 23 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 108 248 (accept_3_2 91 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 248 2 45 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 248 (Polychromatic418967fa.accept_16_9_12_8_1_1554 89 108 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 248 4 22 27 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 108 248
  (Polychromatic418967fa.accept_15_12_3_8_1_5245 87 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 108 248 2 43 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 108 248 (accept_3_2 85 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 248 4 21 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 248 (Polychromatic418967fa.accept_13_5_4_1_1_364 83 108 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 248 2 41 54 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 108 248
  (Polychromatic418967fa.accept_13_3_4_1_1_363 81 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 108 248 4 20 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 108 248 (accept_3_2 79 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 248 2 39 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 248 (Polychromatic418967fa.accept_16_13_12_8_1_2451 77 108 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 248 4 19 27 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 108 248
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 75 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 108 248 2 37 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 108 248 (accept_3_2 73 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 248 4 18 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 248 (Polychromatic418967fa.accept_15_11_3_8_1_750 71 108 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 248 2 35 54 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 248
  (Polychromatic418967fa.accept_11_3_9_6_1_105 69 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 248 4 17 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 248 (accept_3_2 67 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 248 2 33 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 248 (Polychromatic418967fa.accept_15_5_3_8_1_748 65 108 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 248 4 16 27 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 248
  (Polychromatic418967fa.accept_16_15_12_8_1_4585 63 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 108 248 2 31 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 108 248 (accept_3_2 61 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 248 4 15 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 248 (Polychromatic418967fa.accept_16_11_12_8_1_1592 59 108 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 248 2 29 54 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 248
  (Polychromatic418967fa.accept_13_5_4_1_1_364 57 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 248 4 14 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 248 (accept_3_2 55 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 248 2 27 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 248 (Polychromatic418967fa.accept_16_5_12_8_1_2521 53 108 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 248 4 13 27 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 248
  (Polychromatic418967fa.accept_16_3_12_8_1_808 51 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 248 2 25 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 248 (accept_3_2 49 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 248 4 12 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 248 (Polychromatic418967fa.accept_11_3_9_6_1_105 47 108 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 248 2 23 54 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 248
  (Polychromatic418967fa.accept_16_13_12_8_1_2451 45 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 108 248 4 11 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 108 248 (accept_3_2 43 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 248 2 21 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 248 (Polychromatic418967fa.accept_15_11_3_8_1_750 41 108 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 248 4 10 27 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 248
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 248 2 19 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 248 (accept_3_2 37 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 248 4 9 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 248 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 108 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 248 2 17 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 248 (Polychromatic418967fa.accept_16_1_12_8_1_2405
  33 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 248 4 8 27 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 248
  (accept_3_2 31 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 248 2 15 54 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 248
  (Polychromatic418967fa.accept_13_3_4_1_1_363 29 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 248 4 7 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 248 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 108 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 248 2 13 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 248 (accept_3_2 25 108 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 248 4 6 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 248 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 108
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 248 2 11 54 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 248
  (Polychromatic418967fa.accept_16_5_12_8_1_2521 21 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 248 4 5 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 248 (accept_3_2 19 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  108 248 2 9 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 248 (Polychromatic418967fa.accept_16_1_12_8_1_2405 17 108 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 248 4 4 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 248
  (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 248 2 7 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 248 (accept_3_2 13 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 248 4 3 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 248 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 108 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 248 2 5 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 248 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9
  108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 248 4 2 27 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 248 (accept_3_2 7
  108 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 248 2 3 54 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 248
  (Polychromatic418967fa.accept_13_5_4_1_1_364 5 108 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 248 4 1 27 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 108 248 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 108 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 248 2 1 54 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 248 (accept_3_2 1 108 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 248 (allA_succ_of_accept 106 107 248 (accept_3_2 106 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 107 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 104 107
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 248 (accept_3_2 103 107
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 102 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 101 107 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 248 (accept_3_2 100 107 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 248 (Polychromatic418967fa.accept_12_2_11_8_1_504
  98 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 248 (accept_3_2 97
  107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 96 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 107 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 95 107 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 248 (accept_3_2 94 107 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 248 (Polychromatic418967fa.accept_7_1_2_3_1_257
  92 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 107 248 (accept_3_2 91
  107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 107 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 90 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 107 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 107 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 248 (accept_3_2 88 107 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 248 (Polychromatic418967fa.accept_12_2_11_8_1_504
  86 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 248 (accept_3_2 85
  107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 107 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 84 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 107 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 107 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 248 (accept_3_2 82 107 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 248 (Polychromatic418967fa.accept_11_3_8_6_1_788
  80 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 248 (accept_3_2 79
  107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 107 248 (Polychromatic418967fa.accept_16_13_11_8_1_2449 77 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 248 (accept_3_2 76 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 248 (accept_3_2 73 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 248 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 248 (accept_3_2 70 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 248 (accept_3_2 67 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 248 (accept_3_2 64 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 248 (accept_3_2 61 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 248 (Polychromatic418967fa.accept_10_9_7_8_1_1184 59 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 248 (accept_3_2 58 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 248 (accept_3_2 55 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 248 (Polychromatic418967fa.accept_16_5_11_8_1_3431 53 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 248 (accept_3_2 52 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 248 (accept_3_2 49 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 248 (accept_3_2 46 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 248
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 248 (accept_3_2 43 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 248 (accept_3_2 40 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 248 (accept_3_2 37 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 248 (accept_3_2 34 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 248
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 248 (accept_3_2 31 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 248 (accept_3_2 28 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 248 (accept_3_2 25 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 248 (Polychromatic418967fa.accept_19_4_12_1_1_3991 23 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 248 (accept_3_2 22 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 248 (accept_3_2 19 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 248 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 248 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 248 (accept_3_2 16 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 248
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 248 (accept_3_2 13 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 248 (accept_3_2 10 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 248 (accept_3_2 7 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 248 (accept_3_2 4 107 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 248 (accept_3_2 1 107 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 248 (allA_of_3_0 106 106 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 248
  (allA_succ_of_accept 104 105 248 (Polychromatic418967fa.accept_19_9_10_1_1_8329 104 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 248 (accept_3_2 103 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 248 (accept_3_2 100 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 248 (Polychromatic418967fa.accept_19_4_10_1_1_2776 99 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 248 (accept_3_2 97 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 248 (Polychromatic418967fa.accept_17_11_3_10_1_2838 96 105 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 248 (accept_3_2 94 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 248 (accept_3_2 91 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 248 (accept_3_2 88 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 248 (Polychromatic418967fa.accept_10_7_5_8_1_1167 87 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 248 (Polychromatic418967fa.accept_24_14_9_8_1_11688 86 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 248 (accept_3_2 85 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 105 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 248 (accept_3_2 82 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 248 (Polychromatic418967fa.accept_14_11_7_10_1_4852 81 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 248 (accept_3_2 79 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 248 (accept_3_2 76 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 248 (accept_3_2 73 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 248 (accept_3_2 70 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 248 (Polychromatic418967fa.accept_25_19_5_23_1_11515 69 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 248 (Polychromatic418967fa.accept_16_4_9_8_1_2509 68 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 248 (accept_3_2 67 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 105 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 248 (accept_3_2 64 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 248 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 248 (accept_3_2 61 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 248 (Polychromatic418967fa.accept_14_4_7_10_1_3888 60 105 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 248 (accept_3_2 58 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 248 (accept_3_2 55 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 248 (accept_3_2 52 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 248 (Polychromatic418967fa.accept_19_13_10_1_1_8236 51 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 248 (Polychromatic418967fa.accept_20_10_5_8_1_6385 50 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 248 (accept_3_2 49 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 105 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 248 (accept_3_2 46 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 248 (Polychromatic418967fa.accept_14_3_7_10_1_2146 45 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 248 (accept_3_2 43 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 248 (accept_3_2 40 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 248 (accept_3_2 37 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 248 (Polychromatic418967fa.accept_16_4_9_8_1_2509 36 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 248 (accept_3_2 34 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 248 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 248 (accept_3_2 31 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 105 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 248 (accept_3_2 28 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 248 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 248 (accept_3_2 25 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 248 (Polychromatic418967fa.accept_17_7_3_10_1_2881 24 105 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 248 (accept_3_2 22 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 248 (accept_3_2 19 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 248 (accept_3_2 16 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 248 (Polychromatic418967fa.accept_16_15_9_8_1_2440 15 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 248 (Polychromatic418967fa.accept_19_14_10_1_1_8316 14 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 248 (accept_3_2 13 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 248 (accept_3_2 10 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 248 (Polychromatic418967fa.accept_17_9_3_10_1_9070 9 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 248 (accept_3_2 7 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 248 (accept_3_2 4 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 248 (accept_3_2 1 105 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 248 (allA_succ_of_accept 103 104 248 (accept_3_2 103 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 248 2 51 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 248 (Polychromatic418967fa.accept_14_3_6_10_1_752 101 104 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 248 4 25 26 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 248
  (Polychromatic418967fa.accept_10_9_4_8_1_741 99 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 248 2 49 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 248 (accept_3_2 97 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 248 8 12 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 95 104 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 248 2 47 52 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 93 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 248 4 23 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 248 (accept_3_2 91 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 248 2 45 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 248 (Polychromatic418967fa.accept_10_9_4_8_1_741 89 104 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 248 8 11 13 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 248
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 87 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 248 2 43 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 248 (accept_3_2 85 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 248 4 21 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 248 (Polychromatic418967fa.accept_17_15_2_10_1_9021 83 104 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 248 2 41 52 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 248 8 10 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 248 (accept_3_2 79 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 248 2 39 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 248 (Polychromatic418967fa.accept_21_14_20_17_1_15009 77 104 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 248 4 19 26 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 248
  (Polychromatic418967fa.accept_22_9_16_6_1_2493 75 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 248 2 37 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 248 (accept_3_2 73 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 248 8 9 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 104 248 (Polychromatic418967fa.accept_19_14_9_1_1_8315 71 104 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 248 2 35 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 248 (Polychromatic418967fa.accept_10_9_4_8_1_741
  69 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 104 248 4 17 26 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 104 248
  (accept_3_2 67 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 104 248 2 33 52 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 104 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 104 248 8 8 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 104 248 (Polychromatic418967fa.accept_17_12_2_10_1_2862 63 104 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 104 248 2 31 52 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 104 248 (accept_3_2 61 104 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 104 248 4 15 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 104 248 (Polychromatic418967fa.accept_10_9_4_8_1_741
  59 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 248 2 29 52 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 248
  (Polychromatic418967fa.accept_22_13_16_6_1_8823 57 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 104 248 8 7 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 104 248 (accept_3_2 55 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 248 2 27 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 104 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 248 4 13 26 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 248 2 25 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 248 (accept_3_2 49 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 248 8 6 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 104 248 (Polychromatic418967fa.accept_27_20_23_5_1_15008 47 104 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 248 2 23 52 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 248
  (Polychromatic418967fa.accept_11_1_5_6_1_397 45 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 248 4 11 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 248 (accept_3_2 43 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 248 2 21 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 248 (Polychromatic418967fa.accept_25_16_4_23_1_15007 41 104 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 248 8 5 13 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 248 2 19 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 248 (accept_3_2 37 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 248 4 9 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 248 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 104 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 248 2 17 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 248 (Polychromatic418967fa.accept_19_14_9_1_1_8315
  33 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 248 8 4 13 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 248
  (accept_3_2 31 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 248 2 15 52 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 248
  (Polychromatic418967fa.accept_10_9_4_8_1_741 29 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 104 248 4 7 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 248 (Polychromatic418967fa.accept_19_8_9_1_1_3990 27 104 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 248 2 13 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 248 (accept_3_2 25 104 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 248 8 3 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 104 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 248 2 11 52 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 248
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 248 4 5 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 248 (accept_3_2 19 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 248 2 9 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 248 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 104 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 248 8 2 13 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 248
  (Polychromatic418967fa.accept_17_15_2_10_1_9021 15 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 104 248 2 7 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 104 248 (accept_3_2 13 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 104 248 4 3 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 104 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 104 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 248 2 5 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 9
  104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 248 8 1 13 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 248 (accept_3_2 7
  104 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 248 2 3 52 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 248
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 104 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 104 248 4 1 26 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 104 248 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 104 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 248 2 1 52 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 248 (accept_3_2 1 104 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 248 (allA_of_3_0 103 103 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 248 (allA_succ_of_accept 101
  102 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 101 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 248 2 50 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 99 102 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 248 2 49 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 248 (accept_3_2 97 102 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 248 2 48 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 95 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 248 2 47 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 248 (Polychromatic418967fa.accept_12_9_6_8_1_518 93 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 248 2 46 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 248 (accept_3_2 91 102 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 248 2 45 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 89
  102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 248 2 44 51 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 102 248
  (Polychromatic418967fa.accept_9_6_3_5_1_240 87 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 102 248 2 43 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 102 248 (accept_3_2 85 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 248 2 42 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 248 2 41 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 102 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 102 248 2 40 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 102 248 (accept_3_2 79 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 248 2 39 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 248 (Polychromatic418967fa.accept_13_12_11_1_1_2920 77 102 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 248 2 38 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 75 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 248 2 37 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 248 (accept_3_2 73 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 248 2 36 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 248 2 35 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 248 2 34 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 248 (accept_3_2 67 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 248 2 33 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 248 2 32 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 248
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 248 2 31 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 248 (accept_3_2 61 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 248 2 30 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 248 (Polychromatic418967fa.accept_13_7_11_1_1_2903 59 102 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 248 2 29 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 248 2 28 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 248 (accept_3_2 55 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 248 2 27 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 248 2 26 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 248
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 248 2 25 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 248 (accept_3_2 49 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 248 2 24 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 248 2 23 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 248 2 22 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 248 (accept_3_2 43 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 248 2 21 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 248 2 20 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 248 2 19 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 248 (accept_3_2 37 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 248 2 18 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 248 2 17 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 248
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 248 2 16 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 248 (accept_3_2 31 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 248 2 15 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 248 2 14 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 248 2 13 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 248 (accept_3_2 25 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 248 2 12 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 248 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 102 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 248 2 11 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 248 2 10 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 248 (accept_3_2 19 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 248 2 9 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 248 2 8 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 248 2 7 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 248 (accept_3_2 13 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 248 2 6 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 248 2 5 51 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 248
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 248 2 4 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 248 (accept_3_2 7 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  248 2 3 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 102 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 248 2 2 51 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 248 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 102 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 248 2 1 51 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 248 (accept_3_2 1 102 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 248 (allA_succ_of_accept 100 101 248 (accept_3_2 100 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 101 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 248 (accept_3_2 97 101 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 248 (Polychromatic418967fa.accept_9_6_2_5_1_506
  96 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 248
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 95 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 248 (accept_3_2 94 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 248 (Polychromatic418967fa.accept_11_4_2_6_1_389 92 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 248 (accept_3_2 91 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 248 (Polychromatic418967fa.accept_14_6_3_10_1_3905 90 101
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 89 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 248 (accept_3_2 88 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 86 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 248 (accept_3_2 85 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 101 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 248
  (Polychromatic418967fa.accept_10_3_1_8_1_132 83 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 248 (accept_3_2 82 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 248 (accept_3_2 79 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 248
  (Polychromatic418967fa.accept_14_7_3_10_1_1364 77 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 248 (accept_3_2 76 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 248 (accept_3_2 73 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 248 (Polychromatic418967fa.accept_15_12_11_8_1_1392 72 101
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 248 (accept_3_2 70 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 248 (Polychromatic418967fa.accept_16_4_5_8_1_2425 68 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 248 (accept_3_2 67 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 101 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 248
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 248 (accept_3_2 64 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 248 (accept_3_2 61 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 248
  (Polychromatic418967fa.accept_10_9_1_8_1_755 59 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 248 (accept_3_2 58 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 248 (Polychromatic418967fa.accept_13_4_10_1_1_1390 56 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 248 (accept_3_2 55 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 248 (Polychromatic418967fa.accept_23_8_9_18_1_5035 54 101
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 248 (accept_3_2 52 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 248 (accept_3_2 49 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 101 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 248
  (Polychromatic418967fa.accept_20_7_1_8_1_10806 47 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 248 (accept_3_2 46 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 248 (accept_3_2 43 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 248
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 41 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 101 248 (accept_3_2 40 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 248 (accept_3_2 37 101
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 248
  (Polychromatic418967fa.accept_16_4_5_8_1_2425 36 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 101 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 248 (accept_3_2 34 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 248
  (Polychromatic418967fa.accept_25_7_1_23_1_15006 32 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 101 248 (accept_3_2 31 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 101 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 248 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 101
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 248 (accept_3_2 28 101
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 101 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 248 (accept_3_2 25 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 101 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 248 (Polychromatic418967fa.accept_10_3_1_8_1_132
  23 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 248 (accept_3_2 22
  101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 101 248 (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 248 (accept_3_2 19 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 101 248 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 248 (accept_3_2 16 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 248 (accept_3_2 13 101 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 101 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 248
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 248 (accept_3_2 10 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 101 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 248 (accept_3_2 7 101 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 248
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 248 (accept_3_2 4 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 248 (accept_3_2 1 101 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 248 (allA_of_3_0 100 100 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 248 (allA_succ_of_accept 98 99
  248 (Polychromatic418967fa.accept_13_7_8_1_1_2145 98 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 248 (accept_3_2 97 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 99 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 248 (accept_3_2 94 99 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 93
  99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 248
  (Polychromatic418967fa.accept_15_2_9_8_1_736 92 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 248 (accept_3_2 91 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 248 (accept_3_2 88 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 248 (Polychromatic418967fa.accept_10_7_9_8_1_1135 87 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 248 (accept_3_2 85 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 248 (accept_3_2 82 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 248
  (Polychromatic418967fa.accept_23_11_7_18_1_13430 80 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 99 248 (accept_3_2 79 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 99 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 99 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 99 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 248 (accept_3_2 76 99 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 75
  99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 248 (accept_3_2 73 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 248 (accept_3_2 70 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 248 (Polychromatic418967fa.accept_16_5_3_8_1_4555 69 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 248 (accept_3_2 67 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 248 (accept_3_2 64 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 248 (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 248
  (Polychromatic418967fa.accept_15_2_9_8_1_736 62 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 248 (accept_3_2 61 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 248 (accept_3_2 58 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 248 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 248
  (Polychromatic418967fa.accept_17_5_14_10_1_2831 56 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 248 (accept_3_2 55 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 248 (accept_3_2 52 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 248
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 50 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 248 (accept_3_2 49 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 248 (Polychromatic418967fa.accept_13_9_8_1_1_824 48 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 248 (accept_3_2 46 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 248 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 248 (accept_3_2 43 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 248 (accept_3_2 40 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 248
  (Polychromatic418967fa.accept_13_12_8_1_1_825 38 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 248 (accept_3_2 37 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 248 (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 248 (accept_3_2 34 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 248 (accept_3_2 31 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 248 (accept_3_2 28 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 248 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 248 (accept_3_2 25 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 248 (accept_3_2 22 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 248 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 248
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 248 (accept_3_2 19 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 248 (accept_3_2 16 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 248 (Polychromatic418967fa.accept_19_15_4_1_1_4060 15 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 248
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 248 (accept_3_2 13 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 248 (accept_3_2 10 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 248
  (Polychromatic418967fa.accept_21_8_15_17_1_4382 8 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 248 (accept_3_2 7 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  248 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 248 (accept_3_2 4 99 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 248 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 99 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  99 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 248 (accept_3_2 1 99 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  248 (allA_succ_of_accept 97 98 248 (accept_3_2 97 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 248 2 48 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 98 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 248 2 47 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 93
  98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 248 2 46 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 248 (accept_3_2 91
  98 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 248 2 45 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 248
  (Polychromatic418967fa.accept_12_5_2_8_1_172 89 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 248 2 44 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 248 2 43 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 248 (accept_3_2 85 98 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 248 2 42 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 83
  98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 248 2 41 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 248
  (Polychromatic418967fa.accept_13_3_7_1_1_334 81 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 248 2 40 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 248 (accept_3_2 79 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 248 2 39 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 248 2 38 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 248 2 37 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 248 (accept_3_2 73 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 248 2 36 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 248 (Polychromatic418967fa.accept_11_5_10_6_1_793 71 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 248 2 35 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 248
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 248 2 34 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 248 (accept_3_2 67 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 248 2 33 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 248 2 32 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 248
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 248 2 31 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 248 (accept_3_2 61 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 248 2 30 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 248 2 29 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 248 2 28 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 248 (accept_3_2 55 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 248 2 27 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 248 2 26 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 248
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 248 2 25 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 248 (accept_3_2 49 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 248 2 24 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 248 2 23 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 248
  (Polychromatic418967fa.accept_13_6_7_1_1_335 45 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 248 2 22 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 248 (accept_3_2 43 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 248 2 21 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 248 2 20 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 248 2 19 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 248 (accept_3_2 37 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 248 2 18 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 248 2 17 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 248
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 248 2 16 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 248 (accept_3_2 31 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 248 2 15 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 248 2 14 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 248
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 248 2 13 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 248 (accept_3_2 25 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 248 2 12 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 248 2 11 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 248 2 10 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 98 248 (accept_3_2 19 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 248 2 9 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 248 2 8 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 248 2 7 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 248 (accept_3_2 13
  98 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 248 2 6 49 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 248 2 5 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 248 (Polychromatic418967fa.accept_17_9_13_10_1_1825 9 98 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 248 2 4 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 248 (accept_3_2 7 98 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 248 2 3 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 248 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 98 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 248 2 2 49 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 98
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 248 2 1 49 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 248 (accept_3_2 1 98
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  248 (allA_of_3_0 97 97 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 248 (allA_succ_of_accept 95 96 248
  (Polychromatic418967fa.accept_13_4_5_1_1_833 95 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 248 2 47 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 93 96 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 248 4 23 24 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 248 (accept_3_2 91 96 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 248 2 45 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 89
  96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 248 8 11 12 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 248
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 87 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 248 2 43 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 248 (accept_3_2 85 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 248 4 21 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 96 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 248 2 41 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 248 (Polychromatic418967fa.accept_13_3_5_1_1_2144
  81 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 248 8 10 12 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 248 (accept_3_2 79
  96 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 248 2 39 48 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 248
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 77 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 248 4 19 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 96 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 96 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 248 2 37 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 248 (accept_3_2 73 96 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 248 8 9 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 96 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 96 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 248 2 35 48 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 248
  (Polychromatic418967fa.accept_11_3_8_6_1_788 69 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 248 4 17 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 248 (accept_3_2 67 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96
  248 2 33 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 96 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 96 248 8 8 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 96 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 96 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 248 2 31 48 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 248 (accept_3_2 61 96 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 248 4 15 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 248 (Polychromatic418967fa.accept_15_14_6_8_1_1410
  59 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 248 2 29 48 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 248 8 7 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 96 248 (accept_3_2 55 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96
  248 2 27 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 96 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 96 248 4 13 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 96 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 96 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 248 2 25 48 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 248 (accept_3_2 49 96 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 248 8 6 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 47
  96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 248 2 23 48 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 248
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 248 4 11 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 248 (accept_3_2 43 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96
  248 2 21 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 96 248 (Polychromatic418967fa.accept_22_19_8_6_1_13504 41 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 96 248 8 5 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 96 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 96 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 248 2 19 48 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 248 (accept_3_2 37 96 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 248 4 9 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 248 2 17 48 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 248
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 248 8 4 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 248 (accept_3_2 31 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  248 2 15 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 96 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 248 4 7 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 248 (Polychromatic418967fa.accept_18_9_6_14_1_5913 27 96 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 248 2 13 48 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 248 (accept_3_2 25 96 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 248 8 3 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 248 2 11 48 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 248 4 5 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 248 (accept_3_2 19 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  248 2 9 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 248 8 2 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 248 2 7 48 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 248 (accept_3_2 13 96 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 248 4 3 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 96 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 248 2 5 48 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 248 8 1 12 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 248 (accept_3_2 7 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 248
  2 3 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  248 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 96 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 96 248 4 1 24 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 96 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 248 2 1 48 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 248 (accept_3_2 1 96 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 96
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 248
  (allA_succ_of_accept 94 95 248 (accept_3_2 94 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 92 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 248 (accept_3_2 91 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 248
  (Polychromatic418967fa.accept_11_1_7_6_1_378 89 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 248 (accept_3_2 88 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 86 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 248 (accept_3_2 85 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 248 (Polychromatic418967fa.accept_16_4_15_8_1_2413 84 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 83 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 248 (accept_3_2 82 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 248 (Polychromatic418967fa.accept_18_8_5_14_1_3353 80 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 248 (accept_3_2 79 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 95 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 248
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 248 (accept_3_2 76 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 248 (accept_3_2 73 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 248 (accept_3_2 70 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 248 (Polychromatic418967fa.accept_13_3_4_1_1_363 68 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 248 (accept_3_2 67 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 248 (Polychromatic418967fa.accept_23_20_3_18_1_10087 66 95 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 248
  (Polychromatic418967fa.accept_16_1_15_8_1_2411 65 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 248 (accept_3_2 64 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 248 (accept_3_2 61 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 248 (Polychromatic418967fa.accept_16_12_15_8_1_4586 60 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 248
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 248 (accept_3_2 58 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 248 (Polychromatic418967fa.accept_11_1_7_6_1_378 56 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 248 (accept_3_2 55 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 248 (Polychromatic418967fa.accept_20_14_15_8_1_9380 54 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 248
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 248 (accept_3_2 52 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 248 (accept_3_2 49 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 248
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 248 (accept_3_2 46 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 248 (Polychromatic418967fa.accept_13_5_4_1_1_364 44 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 248 (accept_3_2 43 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 248 (accept_3_2 40 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 248 (accept_3_2 37 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 248
  (Polychromatic418967fa.accept_14_7_11_10_1_2155 35 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 248 (accept_3_2 34 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 248 (accept_3_2 31 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 248 (Polychromatic418967fa.accept_20_10_15_8_1_4818 30 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 248 (accept_3_2 28 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 248 (accept_3_2 25 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 248 (Polychromatic418967fa.accept_29_24_8_16_1_15005 24 95 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 248
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 248 (accept_3_2 22 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 248 (accept_3_2 19 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 248 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 248
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 248 (accept_3_2 16 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 248 (accept_3_2 13 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 248
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 248 (accept_3_2 10 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 248 (accept_3_2 7 95 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 95 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 248
  (Polychromatic418967fa.accept_13_5_4_1_1_364 5 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 248 (accept_3_2 4 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 95 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 248 (accept_3_2 1 95 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 248
  (allA_of_3_0 94 94 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 248 (allA_succ_of_accept 92 93 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 92 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 248 (accept_3_2 91 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 90 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 248 (accept_3_2 88 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 248
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 86 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 248 (accept_3_2 85 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 248 (Polychromatic418967fa.accept_13_6_2_1_1_2137 84 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 248 (accept_3_2 82 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 248 (Polychromatic418967fa.accept_10_1_3_8_1_136 81 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 248
  (Polychromatic418967fa.accept_9_8_3_5_1_241 80 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 248 (accept_3_2 79 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 248 (accept_3_2 76 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 248 (accept_3_2 73 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 248 (Polychromatic418967fa.accept_15_12_3_8_1_5245 72 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 248 (accept_3_2 70 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 248 (accept_3_2 67 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 66 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 248 (accept_3_2 64 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 248 (Polychromatic418967fa.accept_17_12_8_10_1_6440 63 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 93 248 31 2 3 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 93 248 (accept_3_2 61 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 93 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 93 248 (accept_3_2 58 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  93 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 93 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 248 (accept_3_2 55 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 248 (accept_3_2 52 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  93 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 93 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 248 (accept_3_2 49 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 248 (accept_3_2 46 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  93 248 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 93 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 248 (accept_3_2 43 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 248 (accept_3_2 40 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  93 248 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 93 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 248 (accept_3_2 37 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 248 (accept_3_2 34 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  93 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 93 248 (Polychromatic418967fa.accept_11_10_5_6_1_1842 32 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 31 93 248 31 1 3 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 30 93 248
  (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 248 (accept_3_2 28 93 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 26
  93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 248 (accept_3_2 25 93
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 248
  (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 248 (accept_3_2 22 93 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 248 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 248 (accept_3_2 19 93
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 248
  (Polychromatic418967fa.accept_12_6_9_8_1_165 18 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 248 (accept_3_2 16 93 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 248
  (Polychromatic418967fa.accept_19_14_17_1_1_2788 14 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 248 (accept_3_2 13 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 248 (accept_3_2 10 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 248 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 93 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 248 (accept_3_2 7 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  248 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 248 (accept_3_2 4 93 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 248 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 93 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 93
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 248 (accept_3_2 1 93 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 248
  (allA_succ_of_accept 91 92 248 (accept_3_2 91 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  248 2 45 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 89 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 248 4 22 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 87 92 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 248 2 43 46 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 248 (accept_3_2 85 92 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 248 4 21 23 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 248
  (Polychromatic418967fa.accept_16_3_12_8_1_808 83 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 248 2 41 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 92 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 248 4 20 23 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 248 (accept_3_2 79 92 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 248 2 39 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 248 (Polychromatic418967fa.accept_16_13_12_8_1_2451
  77 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 248 4 19 23 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 248 2 37 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 248 (accept_3_2 73 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 248 4 18 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 92 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 92 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 248 2 35 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 69
  92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 248 4 17 23 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 248 (accept_3_2 67
  92 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 248 2 33 46 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 248 4 16 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 248 (Polychromatic418967fa.accept_16_15_12_8_1_4585 63 92 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 248 2 31 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 248 (accept_3_2 61 92 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 248 4 15 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 248 (Polychromatic418967fa.accept_16_11_12_8_1_1592 59 92
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 248 2 29 46 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 248 4 14 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 248 (accept_3_2 55 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  248 2 27 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 92 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 248 4 13 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 92 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 248 2 25 46 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 248 (accept_3_2 49 92 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 248 4 12 23 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 248 2 23 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 92 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 92 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 248 4 11 23 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 248 (accept_3_2 43 92 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 248 2 21 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 248 (Polychromatic418967fa.accept_16_9_12_8_1_1554
  41 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 248 4 10 23 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 248 2 19 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 92 248 (accept_3_2 37 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 248 4 9 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 92 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 248 2 17 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 248 4 8 23 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 248 (accept_3_2 31
  92 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 248 2 15 46 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 248
  (Polychromatic418967fa.accept_16_13_12_8_1_2451 29 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 248 4 7 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 248 (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 92 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 248 2 13 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 248 (accept_3_2 25 92 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 248 4 6 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 92 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 92 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 248 2 11 46 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 248 4 5 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 248 (accept_3_2 19 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  248 2 9 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 248 4 4 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 92 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 248 2 7 46 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 248 (accept_3_2 13 92 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 248 4 3 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 92 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 248 2 5 46 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 248 4 2 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 248 (accept_3_2 7 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 248
  2 3 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  248 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 92 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 248 4 1 23 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 92 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 248 2 1 46 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 248 (accept_3_2 1 92 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 248
  (allA_of_3_0 91 91 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 248 (allA_succ_of_accept 89 90 248
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 89 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 248 2 44 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 90 248 (Polychromatic418967fa.accept_12_3_6_8_1_969 87 90 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 248 2 43 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 248 (accept_3_2 85 90 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 248 2 42 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 248 (Polychromatic418967fa.accept_13_5_12_1_1_2123
  83 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 248 2 41 45 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 248 2 40 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 248 (accept_3_2 79 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 248 2 39 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 248 (Polychromatic418967fa.accept_20_17_10_8_1_9374 77 90 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 248 2 38 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 248 2 37 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 90 248 (accept_3_2 73 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 248 2 36 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 248 (Polychromatic418967fa.accept_24_23_18_8_1_4564 71 90 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 248 2 35 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 248 2 34 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 90 248 (accept_3_2 67 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 248 2 33 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 90 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 248 2 32 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 248 2 31 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 248 (accept_3_2 61 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 248 2 30 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 248 (Polychromatic418967fa.accept_11_4_2_6_1_389 59 90 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 248 2 29 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 248 2 28 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 90 248 (accept_3_2 55 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 248 2 27 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 90 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 248 2 26 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 248 2 25 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 90 248 (accept_3_2 49 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 248 2 24 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 248 (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 90 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 248 2 23 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 248 2 22 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 90 248 (accept_3_2 43 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 248 2 21 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 248 (Polychromatic418967fa.accept_13_2_12_1_1_343 41 90 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 248 2 20 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 248 2 19 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 90 248 (accept_3_2 37 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 248 2 18 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 248 (Polychromatic418967fa.accept_20_15_10_8_1_6398 35 90 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 248 2 17 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 248 2 16 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 248 (accept_3_2 31 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 248 2 15 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 248 (Polychromatic418967fa.accept_17_12_5_10_1_5160 29 90 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 248 2 14 45 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 248 2 13 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 90 248 (accept_3_2 25 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 248 2 12 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 90 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 248 2 11 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 248 2 10 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 90 248 (accept_3_2 19 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 248 2 9 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 248 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 90 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 248 2 8 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 248 (Polychromatic418967fa.accept_11_4_2_6_1_389 15
  90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 248 2 7 45 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 248 (accept_3_2 13
  90 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 248 2 6 45 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 248 2 5 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 248 2 4 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 248 (accept_3_2 7 90 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 90 248 2 3 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 90 248 (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 90 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 248 2 2 45 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 248 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  90 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 248 2 1 45 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 248 (accept_3_2 1 90
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 248
  (allA_succ_of_accept 88 89 248 (accept_3_2 88 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 248 (accept_3_2 85 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 248 (accept_3_2 82 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 248 (Polychromatic418967fa.accept_15_5_14_8_1_1376 80 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 248 (accept_3_2 79 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 89 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 248
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 77 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 248 (accept_3_2 76 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 248 (accept_3_2 73 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 248 (accept_3_2 70 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 248 (Polychromatic418967fa.accept_13_3_11_1_1_2122 68 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 248 (accept_3_2 67 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 89 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 248 (accept_3_2 64 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 248 (Polychromatic418967fa.accept_11_7_1_6_1_1281 62 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 248 (accept_3_2 61 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 248
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 59 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 248 (accept_3_2 58 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 248 (accept_3_2 55 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 248
  (Polychromatic418967fa.accept_21_11_5_17_1_760 53 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 248 (accept_3_2 52 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 248 (accept_3_2 49 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 248 (accept_3_2 46 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 248 (accept_3_2 43 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 248
  (Polychromatic418967fa.accept_10_1_9_8_1_123 41 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 248 (accept_3_2 40 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 248 (accept_3_2 37 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 248
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 248 (accept_3_2 34 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 248 (Polychromatic418967fa.accept_17_15_4_10_1_3968 32 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 248 (accept_3_2 31 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 89 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 248 (accept_3_2 28 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 248 (accept_3_2 25 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 248 (accept_3_2 22 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 248 (accept_3_2 19 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 248 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 248
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 248 (accept_3_2 16 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 248 (accept_3_2 13 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 248 (accept_3_2 10 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 248 (accept_3_2 7 89 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 89 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 248
  (Polychromatic418967fa.accept_11_5_1_6_1_774 5 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 248 (accept_3_2 4 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 89 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 248 (accept_3_2 1 89 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 248 (allA_of_3_0 88 88 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 248
  (allA_succ_of_accept 86 87 248 (Polychromatic418967fa.accept_13_8_9_1_1_2147 86 87 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 248 (accept_3_2 85 87 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 248 (accept_3_2 82 87
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 248
  (Polychromatic418967fa.accept_16_1_7_8_1_3422 81 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 87 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 248 (accept_3_2 79 87 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 248 (accept_3_2 76 87
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63
  75 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 74 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 248 (accept_3_2 73 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 248 (Polychromatic418967fa.accept_19_15_11_1_1_12437 72 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 248 (accept_3_2 70 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 248 (Polychromatic418967fa.accept_10_9_7_8_1_1184 69 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 248
  (Polychromatic418967fa.accept_16_4_7_8_1_5753 68 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 248 (accept_3_2 67 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 248 (accept_3_2 64 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 248 (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 248 (accept_3_2 61 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 248 (Polychromatic418967fa.accept_11_5_10_6_1_793 60 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 248 (accept_3_2 58 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 248 (accept_3_2 55 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 248 (accept_3_2 52 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 248 (Polychromatic418967fa.accept_21_9_3_17_1_4365 51 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 248
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 50 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 248 (accept_3_2 49 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 248 (accept_3_2 46 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 248 (accept_3_2 43 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 248 (accept_3_2 40 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 248 (accept_3_2 37 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 248 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 248 (accept_3_2 34 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 248 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 248
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 32 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 248 (accept_3_2 31 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 248 (accept_3_2 28 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 248 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 248 (accept_3_2 25 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 248 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 248 (accept_3_2 22 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 248 (accept_3_2 19 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 248 (accept_3_2 16 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 87 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 248
  (Polychromatic418967fa.accept_21_14_3_17_1_15004 14 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 87 248 (accept_3_2 13 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 248 (accept_3_2 10 87 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 248 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9
  87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 248 (accept_3_2 7 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  248 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 248 (accept_3_2 4 87 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  87 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 248 (accept_3_2 1 87 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 248
  (allA_succ_of_accept 85 86 248 (accept_3_2 85 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  248 2 42 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 248 2 41 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 248 (Polychromatic418967fa.accept_23_12_17_18_1_15003 81 86 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 248 2 40 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 248 (accept_3_2 79
  86 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 248 2 39 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 248
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 248 2 38 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 248 2 37 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 248 (accept_3_2 73 86 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 248 2 36 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 71
  86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 248 2 35 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 248 2 34 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 248 (accept_3_2 67 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 248 2 33 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 248 2 32 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 248
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 248 2 31 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 248 (accept_3_2 61 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 248 2 30 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 248 2 29 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 248 2 28 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 248 (accept_3_2 55 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 248 2 27 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 248 2 26 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 248
  (Polychromatic418967fa.accept_13_12_8_1_1_825 51 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 248 2 25 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 248 (accept_3_2 49 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 248 2 24 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 248 2 23 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 248
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 248 2 22 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 248 (accept_3_2 43 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 248 2 21 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 248 2 20 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 248
  (Polychromatic418967fa.accept_23_16_17_18_1_13399 39 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 86 248 2 19 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 86 248 (accept_3_2 37 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 248 2 18 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 248 2 17 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 248 2 16 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 248 (accept_3_2 31 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 248 2 15 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 248 2 14 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 248 2 13 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 248 (accept_3_2 25 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 248 2 12 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 248 2 11 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 248
  (Polychromatic418967fa.accept_24_21_14_8_1_13333 21 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 86 248 2 10 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 86 248 (accept_3_2 19 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 248 2 9 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 86 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 248 2 8 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 248 2 7 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 248 (accept_3_2 13
  86 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 248 2 6 43 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 248
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 248 2 5 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 248 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 86 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 248 2 4 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 248 (accept_3_2 7 86 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 248 2 3 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 86 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 248 2 2 43 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3
  86 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 248 2 1 43 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 248 (accept_3_2 1 86
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 248
  (allA_of_3_0 85 85 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 248 (allA_succ_of_accept 83 84 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 248 2 41 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 248 (Polychromatic418967fa.accept_13_3_6_1_1_3797 81 84 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 248 4 20 21 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 248 (accept_3_2 79 84 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 248 2 39 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 248 (Polychromatic418967fa.accept_15_2_9_8_1_736 77
  84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 248 4 19 21 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 248
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 75 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 248 2 37 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 248 (accept_3_2 73 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 248 4 18 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 248 2 35 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 69
  84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 248 4 17 21 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 248 (accept_3_2 67
  84 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 248 2 33 42 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 248 4 16 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 248 (Polychromatic418967fa.accept_15_3_9_8_1_3164 63 84 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 248 2 31 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 248 (accept_3_2 61 84 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 248 4 15 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 248 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 84 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 248 2 29 42 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 248
  (Polychromatic418967fa.accept_13_5_6_1_1_822 57 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 248 4 14 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 248 (accept_3_2 55 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  248 2 27 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 84 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 248 4 13 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 248 2 25 42 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 248 (accept_3_2 49 84 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 248 4 12 21 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 248 2 23 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 84 248 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 84 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 248 4 11 21 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 248 (accept_3_2 43 84 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 248 2 21 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 248 (Polychromatic418967fa.accept_13_2_6_1_1_3807
  41 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 248 4 10 21 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 248
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 248 2 19 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 84 248 (accept_3_2 37 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 248 4 9 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 248 2 17 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 33
  84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 248 4 8 21 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 248 (accept_3_2 31
  84 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 248 2 15 42 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 248 4 7 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 248 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 84 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 248 2 13 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 248 (accept_3_2 25 84 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 248 4 6 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 84 248 (Polychromatic418967fa.accept_11_1_7_6_1_378 23 84 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 248 2 11 42 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 248
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 248 4 5 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 248 (accept_3_2 19 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  248 2 9 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 248 4 4 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 248 2 7 42 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 248 (accept_3_2 13 84 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 248 4 3 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 248 2 5 42 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 248
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 248 4 2 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 248 (accept_3_2 7 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 248
  2 3 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  248 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 84 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 248 4 1 21 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 248 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 84 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 248 2 1 42 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 248 (accept_3_2 1 84 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 248 (allA_succ_of_accept 82 83 248 (accept_3_2 82 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 83 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 83 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 248 (accept_3_2 79 83 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 78
  83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 248
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 77 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 248 (accept_3_2 76 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 248 (accept_3_2 73 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 248 (accept_3_2 70 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 248 (Polychromatic418967fa.accept_13_3_5_1_1_2144 68 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 248 (accept_3_2 67 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 248 (accept_3_2 64 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 248 (accept_3_2 61 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 248
  (Polychromatic418967fa.accept_14_3_13_10_1_761 59 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 248 (accept_3_2 58 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 248 (accept_3_2 55 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 248 (Polychromatic418967fa.accept_20_14_3_8_1_4914 54 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 248 (accept_3_2 52 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 248 (accept_3_2 49 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 248
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 47 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 248 (accept_3_2 46 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 248 (accept_3_2 43 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 248
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 248 (accept_3_2 40 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 248 (accept_3_2 37 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 248 (accept_3_2 34 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 248 (accept_3_2 31 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 248
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 248 (accept_3_2 28 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 248 (accept_3_2 25 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 248 (accept_3_2 22 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 248 (Polychromatic418967fa.accept_16_4_3_8_1_2486 20 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 248 (accept_3_2 19 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 248 (accept_3_2 16 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 248 (accept_3_2 13 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 248 (accept_3_2 10 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 248 (accept_3_2 7 83 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 248
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 248 (accept_3_2 4 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 83 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 248 (accept_3_2 1 83 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 248 (allA_of_3_0 82 82 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 248
  (allA_succ_of_accept 80 81 248 (Polychromatic418967fa.accept_13_2_3_1_1_3823 80 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 248 (accept_3_2 79 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 248 (accept_3_2 76 81
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 248
  (Polychromatic418967fa.accept_18_3_9_14_1_2219 75 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 248 (Polychromatic418967fa.accept_15_14_6_8_1_1410 74 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 248 (accept_3_2 73 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 248 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 248 (accept_3_2 70 81
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 248 (Polychromatic418967fa.accept_11_2_4_6_1_2412 68 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 248 (accept_3_2 67 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 248 (accept_3_2 64 81
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 248
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 248 (accept_3_2 61 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 248 (Polychromatic418967fa.accept_16_12_1_8_1_5767 60 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 248 (accept_3_2 58 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 248 (Polychromatic418967fa.accept_13_4_3_1_1_2898 56 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 248 (accept_3_2 55 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 248 (accept_3_2 52 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 248 (Polychromatic418967fa.accept_20_11_1_8_1_13623 51 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 248 (accept_3_2 49 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 248 (accept_3_2 46 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 248 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 248 (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 248 (accept_3_2 43 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 248 (accept_3_2 40 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 248 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 248 (Polychromatic418967fa.accept_20_18_1_8_1_9326 38 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 248 (accept_3_2 37 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 248 (accept_3_2 34 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 248 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 248 (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 248 (accept_3_2 31 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 248 (accept_3_2 28 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 248 (Polychromatic418967fa.accept_17_9_13_10_1_1825 26 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 248 (accept_3_2 25 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 248 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 81 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 248 (accept_3_2 22 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 248 (Polychromatic418967fa.accept_14_7_11_10_1_2155 21 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 248 (accept_3_2 19 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 248 (accept_3_2 16 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 248 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 248 (accept_3_2 13 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 248 (Polychromatic418967fa.accept_16_12_1_8_1_5767 12 81
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 248 (accept_3_2 10 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 248 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 248 (accept_3_2 7 81 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 248 (accept_3_2 4 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  248 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 81 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 248 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 248 (accept_3_2 1 81 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 248 (allA_succ_of_accept 79 80 248 (accept_3_2 79 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 80 248 2 39 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 80 248 (Polychromatic418967fa.accept_13_12_2_1_1_2909 77 80 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 80 248 4 19 20 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 80 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 80 248 2 37 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 80 248 (accept_3_2 73 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 80 248 8 9 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 80 248 (Polychromatic418967fa.accept_13_6_2_1_1_2137 71 80 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 248 2 35 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 69
  80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 248 4 17 20 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 248 (accept_3_2 67
  80 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 248 2 33 40 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 80 248 8 8 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 80 248 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 80 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 248 2 31 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 248 (accept_3_2 61 80 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 248 4 15 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 248 (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 80 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 248 2 29 40 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 248 8 7 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 248 (accept_3_2 55 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  248 2 27 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 80 248 (Polychromatic418967fa.accept_11_9_3_6_1_797 53 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 248 4 13 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 80 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 248 2 25 40 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 248 (accept_3_2 49 80 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 248 8 6 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 47
  80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 248 2 23 40 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 248
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 248 4 11 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 248 (accept_3_2 43 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  248 2 21 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 80 248 (Polychromatic418967fa.accept_11_8_3_6_1_1855 41 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 248 8 5 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 80 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 80 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 248 2 19 40 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 248 (accept_3_2 37 80 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 248 4 9 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 248 (Polychromatic418967fa.accept_13_9_2_1_1_813 35 80 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 248 2 17 40 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 248
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 248 8 4 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 248 (accept_3_2 31 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  248 2 15 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 80 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 248 4 7 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 248 (Polychromatic418967fa.accept_15_12_5_8_1_5247 27 80 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 248 2 13 40 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 248 (accept_3_2 25 80 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 248 8 3 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 248 (Polychromatic418967fa.accept_17_6_12_10_1_7781 23 80
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 248 2 11 40 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 248 4 5 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 248 (accept_3_2 19 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  248 2 9 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 248 (Polychromatic418967fa.accept_19_17_4_1_1_2763 17 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 248 8 2 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 80 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 248 2 7 40 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 248 (accept_3_2 13 80 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 248 4 3 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 248 2 5 40 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 248
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 248 8 1 10 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 248 (accept_3_2 7 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 248
  2 3 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  248 (Polychromatic418967fa.accept_17_5_12_10_1_3963 5 80 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 80 248 4 1 20 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 248 2 1 40 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 248 (accept_3_2 1 80 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 248 (allA_of_3_0 79 79 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 248
  (allA_succ_of_accept 77 78 248 (Polychromatic418967fa.accept_21_14_15_17_1_2972 77 78 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 248 2 38 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 75
  78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 248 2 37 39 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 248 (accept_3_2 73
  78 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 248 2 36 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 248 2 35 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 78 248 (Polychromatic418967fa.accept_12_9_6_8_1_518 69 78 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 248 2 34 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 248 (accept_3_2 67 78 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 248 2 33 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 65
  78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 248 2 32 39 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 248 2 31 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 248 (accept_3_2 61 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 248 2 30 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 248 (Polychromatic418967fa.accept_22_15_12_6_1_8744 59 78 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 248 2 29 39 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 248 2 28 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 248 (accept_3_2 55 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 248 2 27 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 78 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 248 2 26 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 248 2 25 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 248 (accept_3_2 49 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 248 2 24 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 78 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 248 2 23 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 248 2 22 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 248 (accept_3_2 43 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 248 2 21 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 248 (Polychromatic418967fa.accept_15_11_3_8_1_750 41 78 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 248 2 20 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 248 2 19 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 78 248 (accept_3_2 37 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 248 2 18 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 248 2 17 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 248 2 16 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 78 248 (accept_3_2 31 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 248 2 15 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 248 2 14 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 248
  (Polychromatic418967fa.accept_11_5_1_6_1_774 27 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 248 2 13 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 248 (accept_3_2 25 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 248 2 12 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 78 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 248 2 11 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 248 2 10 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 248 (accept_3_2 19 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 248 2 9 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 78 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 248 2 8 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 248 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 248 2 7 39 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 248 (accept_3_2 13
  78 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 248 2 6 39 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 78 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 248 2 5 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 248 2 4 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 248 (accept_3_2 7 78 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 248 2 3 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 78 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 248 2 2 39 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 78
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 248 2 1 39 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 248 (accept_3_2 1 78
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 248
  (allA_succ_of_accept 76 77 248 (accept_3_2 76 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 248 (accept_3_2 73 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 248 (Polychromatic418967fa.accept_21_9_14_17_1_12039 72 77 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 248
  (Polychromatic418967fa.accept_17_3_9_10_1_9045 71 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 248 (accept_3_2 70 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 248 (Polychromatic418967fa.accept_16_4_13_8_1_3424 68 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 248 (accept_3_2 67 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 248 (Polychromatic418967fa.accept_15_6_2_8_1_2223 66 77 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 248
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 248 (accept_3_2 64 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 248 (accept_3_2 61 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 248 (Polychromatic418967fa.accept_13_8_12_1_1_4662 60 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 248
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 59 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 248 (accept_3_2 58 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 248 (Polychromatic418967fa.accept_23_10_8_18_1_15002 56 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 248 (accept_3_2 55 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 248 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 77 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 248
  (Polychromatic418967fa.accept_14_11_7_10_1_4852 53 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 248 (accept_3_2 52 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 248 (accept_3_2 49 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 248 (Polychromatic418967fa.accept_22_4_11_6_1_10486 48 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 248
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 248 (accept_3_2 46 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 248 (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 248 (accept_3_2 43 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 248 (Polychromatic418967fa.accept_22_20_11_6_1_13497 42 77
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 248
  (Polychromatic418967fa.accept_13_2_12_1_1_343 41 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 248 (accept_3_2 40 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 248 (accept_3_2 37 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 248 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 248
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 248 (accept_3_2 34 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 248 (Polychromatic418967fa.accept_14_4_7_10_1_3888 32 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 248 (accept_3_2 31 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 248 (Polychromatic418967fa.accept_17_13_9_10_1_2888 30 77
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 248
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 248 (accept_3_2 28 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 248 (accept_3_2 25 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 248 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 248
  (Polychromatic418967fa.accept_21_2_14_17_1_1689 23 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 248 (accept_3_2 22 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 248 (Polychromatic418967fa.accept_16_4_13_8_1_3424 20 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 248 (accept_3_2 19 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 248 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 77
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 248
  (Polychromatic418967fa.accept_14_3_7_10_1_2146 17 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 248 (accept_3_2 16 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 248 (accept_3_2 13 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 248 (Polychromatic418967fa.accept_16_12_13_8_1_2409 12 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 248
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 248 (accept_3_2 10 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 248 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 248 (accept_3_2 7 77 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 248 (Polychromatic418967fa.accept_15_6_2_8_1_2223 6 77 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 248
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 248 (accept_3_2 4 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 77 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 248 (accept_3_2 1 77 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 248 (allA_of_3_0 76 76 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 248 (allA_succ_of_accept 74 75
  248 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 248 (accept_3_2 73 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 248 (accept_3_2 70 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 248
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 68 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 248 (accept_3_2 67 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 248 (accept_3_2 64 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 248 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 248
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 248 (accept_3_2 61 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 248 (accept_3_2 58 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 248 (accept_3_2 55 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 248 (accept_3_2 52 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 248 (accept_3_2 49 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 248 (Polychromatic418967fa.accept_13_9_10_1_1_1389 48 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 248 (accept_3_2 46 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 248 (Polychromatic418967fa.accept_16_13_11_8_1_2449 45 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 248 (accept_3_2 43 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 248 (accept_3_2 40 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 248 (Polychromatic418967fa.accept_26_13_23_14_1_15001 39 75 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 248 (accept_3_2 37 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 248 (accept_3_2 34 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 248
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 248 (accept_3_2 31 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 248 (accept_3_2 28 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 248 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 248
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 248 (accept_3_2 25 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 248 (accept_3_2 22 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 248 (Polychromatic418967fa.accept_16_5_11_8_1_3431 21 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 248 (accept_3_2 19 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 248 (accept_3_2 16 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 248
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 248 (accept_3_2 13 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 248 (accept_3_2 10 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 248 (accept_3_2 7 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  248 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 248 (accept_3_2 4 75 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 248 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 75 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 75
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 248 (accept_3_2 1 75 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 248 (allA_succ_of_accept
  73 74 248 (accept_3_2 73 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 248 2 36 37 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 248 2 35 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 74 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 248 2 34 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 248 (accept_3_2 67 74 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 248 2 33 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 65
  74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 248 2 32 37 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 248
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 248 2 31 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 74 248 (accept_3_2 61 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 248 2 30 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 248 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 74 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 248 2 29 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 248 2 28 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 248 (accept_3_2 55 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 248 2 27 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 248 2 26 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 248 2 25 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 248 (accept_3_2 49 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 248 2 24 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 248 (Polychromatic418967fa.accept_11_3_8_6_1_788 47 74 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 248 2 23 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 248
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 248 2 22 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 248 (accept_3_2 43 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 248 2 21 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 74 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 248 2 20 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 248 2 19 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 248 (accept_3_2 37 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 248 2 18 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 248 2 17 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 248 2 16 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 248 (accept_3_2 31 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 248 2 15 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 74 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 248 2 14 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 248 2 13 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 248 (accept_3_2 25 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 248 2 12 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 74 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 248 2 11 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 248 2 10 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 248 (accept_3_2 19 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 248 2 9 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 74 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 248 2 8 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 248 2 7 37 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 248 (accept_3_2 13
  74 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 248 2 6 37 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 248
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 248 2 5 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 248 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 74 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 248 2 4 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 248 (accept_3_2 7 74 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 248 2 3 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 74 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 248 2 2 37 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 74
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 248 2 1 37 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 248 (accept_3_2 1 74
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 248 (allA_of_3_0 73 73 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 248 (allA_succ_of_accept 71 72 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 248 2 35 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 72 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 248 4 17 18 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 248 (accept_3_2 67 72 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 248 2 33 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 65
  72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 248 8 8 9 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 248
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 248 2 31 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 72 248 (accept_3_2 61 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 248 4 15 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 248 (Polychromatic418967fa.accept_19_2_15_1_1_3977 59 72 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 248 2 29 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 57
  72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 248 8 7 9 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 248 (accept_3_2 55
  72 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 248 2 27 36 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 248
  (Polychromatic418967fa.accept_25_3_22_23_1_13276 53 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 72 248 4 13 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 72 248 (Polychromatic418967fa.accept_25_1_22_23_1_11557 51 72 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 248 2 25 36 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 248 (accept_3_2 49 72 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 248 8 6 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 248 2 23 36 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 248 4 11 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 248 (accept_3_2 43 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  248 2 21 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 72 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 248 8 5 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 72 248 (Polychromatic418967fa.accept_21_18_9_17_1_4409 39 72 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 248 2 19 36 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 248 (accept_3_2 37 72 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 248 4 9 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 35
  72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 248 2 17 36 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 248 8 4 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 248 (accept_3_2 31 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  248 2 15 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 72 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 248 4 7 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 248 2 13 36 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 248 (accept_3_2 25 72 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 248 8 3 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 248 (Polychromatic418967fa.accept_17_6_4_10_1_5176 23 72 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 248 2 11 36 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 248
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 248 4 5 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 248 (accept_3_2 19 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  248 2 9 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 248 (Polychromatic418967fa.accept_19_17_15_1_1_8300 17 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 248 8 2 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 248 2 7 36 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 248 (accept_3_2 13 72 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 248 4 3 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 248 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 72 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 248 2 5 36 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 248
  (Polychromatic418967fa.accept_23_9_3_18_1_8511 9 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 248 8 1 9 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 248 (accept_3_2 7 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 248
  2 3 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  248 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 248 4 1 18 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 72 248 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 72 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 248 2 1 36 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 248 (accept_3_2 1 72 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 248
  (allA_succ_of_accept 70 71 248 (accept_3_2 70 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 248 (accept_3_2 67 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 248 (accept_3_2 64 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 248 (accept_3_2 61 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 248
  (Polychromatic418967fa.accept_10_9_1_8_1_755 59 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 248 (accept_3_2 58 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 248 (accept_3_2 55 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 248 (accept_3_2 52 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 248 (accept_3_2 49 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 248 (accept_3_2 46 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 248 (accept_3_2 43 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 248
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 248 (accept_3_2 40 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 248 (accept_3_2 37 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 248 (Polychromatic418967fa.accept_16_4_7_8_1_5753 36 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 248
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 248 (accept_3_2 34 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 248 (accept_3_2 31 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 248 (accept_3_2 28 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 248 (accept_3_2 25 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 248 (accept_3_2 22 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 248 (accept_3_2 19 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 248
  (Polychromatic418967fa.accept_16_1_7_8_1_3422 17 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 248 (accept_3_2 16 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 248 (accept_3_2 13 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 248 (accept_3_2 10 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 248 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 248 (accept_3_2 7 71 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 71 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 248 (accept_3_2 4 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 71 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 248 (accept_3_2 1 71 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 248
  (allA_of_3_0 70 70 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 248 (allA_succ_of_accept 68 69 248
  (Polychromatic418967fa.accept_13_3_4_1_1_363 68 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 248 (accept_3_2 67 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 248 (accept_3_2 64 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 248 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 69 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 248 (accept_3_2 61 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 248 (accept_3_2 58 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 69 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 248 (accept_3_2 55 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 248 (accept_3_2 52 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 69 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 248
  (Polychromatic418967fa.accept_27_23_15_5_1_15000 50 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 69 248 (accept_3_2 49 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 69 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 248 (accept_3_2 46 69 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 248 (Polychromatic418967fa.accept_14_3_13_10_1_761
  45 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 248 (accept_3_2 43 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 248 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 248 (accept_3_2 40 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 248 (accept_3_2 37 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 248 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 248 (accept_3_2 34 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 248 (Polychromatic418967fa.accept_15_3_9_8_1_3164 33 69 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 248 (accept_3_2 31 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 248 (accept_3_2 28 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 248 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 69 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 248 (accept_3_2 25 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 248 (accept_3_2 22 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 248 (accept_3_2 19 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 248 (accept_3_2 16 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 248 (Polychromatic418967fa.accept_21_15_6_17_1_7466 15 69 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 248
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 248 (accept_3_2 13 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 248 (accept_3_2 10 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 248 (accept_3_2 7 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  248 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 248 (accept_3_2 4 69 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 69 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  69 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 248 (accept_3_2 1 69 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 248 (allA_succ_of_accept 67 68
  248 (accept_3_2 67 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 248 2 33 34 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 248 4 16 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 248 (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 68 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 248 2 31 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 248 (accept_3_2 61 68 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 248 4 15 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 248 (Polychromatic418967fa.accept_11_4_2_6_1_389 59 68 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 248 2 29 34 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 248 4 14 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 248 (accept_3_2 55 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  248 2 27 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 68 248 (Polychromatic418967fa.accept_16_5_4_8_1_1560 53 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 248 4 13 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 68 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 248 2 25 34 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 248 (accept_3_2 49 68 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 248 4 12 17 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 248
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 248 2 23 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 68 248 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 68 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 248 4 11 17 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 248 (accept_3_2 43 68 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 248 2 21 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 248 (Polychromatic418967fa.accept_13_2_3_1_1_3823
  41 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 248 4 10 17 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 248
  (Polychromatic418967fa.accept_16_7_4_8_1_2487 39 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 248 2 19 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 68 248 (accept_3_2 37 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 68 248 4 9 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 68 248 (Polychromatic418967fa.accept_16_3_4_8_1_3450 35 68 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 248 2 17 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 248 (Polychromatic418967fa.accept_13_7_3_1_1_814 33
  68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 248 4 8 17 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 248 (accept_3_2 31
  68 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 248 2 15 34 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 68 248 4 7 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 68 248 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 68 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 248 2 13 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 248 (accept_3_2 25 68 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 248 4 6 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 68 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 68 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 248 2 11 34 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 248
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 21 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 248 4 5 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 248 (accept_3_2 19 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  248 2 9 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 248 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 248 4 4 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 68 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 248 2 7 34 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 248 (accept_3_2 13 68 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 248 4 3 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 248 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 68 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 248 2 5 34 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 248 4 2 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 248 (accept_3_2 7 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 248
  2 3 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  248 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 68 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 248 4 1 17 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 248 (Polychromatic418967fa.accept_16_3_4_8_1_3450 3 68 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 248 2 1 34 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 248 (accept_3_2 1 68 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  67 248 (allA_of_3_0 67 67 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 248 (allA_succ_of_accept 65 66
  248 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 248 2 32 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 66 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 248 2 31 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 248 (accept_3_2 61 66 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 248 2 30 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 248 (Polychromatic418967fa.accept_15_14_6_8_1_1410
  59 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 248 2 29 33 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 248 2 28 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 248 (accept_3_2 55 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 248 2 27 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 248 2 26 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 248
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 248 2 25 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 248 (accept_3_2 49 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 248 2 24 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 66 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 248 2 23 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 248 2 22 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 248 (accept_3_2 43 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 248 2 21 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 248 (Polychromatic418967fa.accept_21_20_3_17_1_13530 41 66 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 248 2 20 33 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 248 2 19 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 248 (accept_3_2 37 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 248 2 18 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 248 2 17 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 248
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 248 2 16 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 248 (accept_3_2 31 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 248 2 15 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 66 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 248 2 14 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 248 2 13 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 248 (accept_3_2 25 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 248 2 12 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 66 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 248 2 11 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 248 2 10 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 248 (accept_3_2 19 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 248 2 9 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 248 2 8 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 248 2 7 33 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 248 (accept_3_2 13
  66 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 248 2 6 33 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 248 2 5 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 248 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 66 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 248 2 4 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 248 (accept_3_2 7 66 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 248 2 3 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 248 (Polychromatic418967fa.accept_17_5_15_10_1_10176 5 66 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 248 2 2 33 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3
  66 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 248 2 1 33 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 248 (accept_3_2 1 66
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 248 (allA_succ_of_accept 64 65 248
  (accept_3_2 64 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 65 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 248 (accept_3_2 61 65 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 248 (Polychromatic418967fa.accept_15_14_5_8_1_3175
  59 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 248 (accept_3_2 58
  65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 248 (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 65 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 248 (accept_3_2 55 65 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 53
  65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 248 (accept_3_2 52 65
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 248 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 248 (accept_3_2 49 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 248 (accept_3_2 46 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 248 (accept_3_2 43 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 248 (accept_3_2 40 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 248
  (Polychromatic418967fa.accept_11_5_10_6_1_793 38 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 248 (accept_3_2 37 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 248 (accept_3_2 34 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 248
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 248 (accept_3_2 31 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 248 (accept_3_2 28 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 248 (accept_3_2 25 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 248 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 248 (accept_3_2 22 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 248 (accept_3_2 19 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 248 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 248 (accept_3_2 16 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 248
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 248 (accept_3_2 13 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 248 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 65 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 248 (accept_3_2 10 65 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 248 (accept_3_2 7 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  248 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 248 (accept_3_2 4 65 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  65 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 248 (accept_3_2 1 65 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 248 (allA_of_3_0 64 64 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 248 (allA_succ_of_accept 62 63 248
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 62 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 248 (accept_3_2 61 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 248 (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 248 (accept_3_2 58 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 248 (Polychromatic418967fa.accept_15_12_3_8_1_5245 57 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 248
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 248 (accept_3_2 55 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 248 (accept_3_2 52 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 248 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 248
  (Polychromatic418967fa.accept_15_5_3_8_1_748 50 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 248 (accept_3_2 49 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 248 (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 248 (accept_3_2 46 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 248 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 248
  (Polychromatic418967fa.accept_16_12_15_8_1_4586 44 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 248 (accept_3_2 43 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 248 (accept_3_2 40 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 248 (Polychromatic418967fa.accept_14_11_7_10_1_4852 39 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 248
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 38 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 248 (accept_3_2 37 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 248 (accept_3_2 34 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 248 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 248
  (Polychromatic418967fa.accept_14_4_7_10_1_3888 32 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 248 (accept_3_2 31 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 248 (accept_3_2 28 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 248 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 248
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 248 (accept_3_2 25 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 248 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 248 (accept_3_2 22 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 248 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 248
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 248 (accept_3_2 19 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 248 (accept_3_2 16 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 248 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 248
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 248 (accept_3_2 13 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 248 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 248 (accept_3_2 10 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 248 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 248
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 248 (accept_3_2 7 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 248 (accept_3_2 4 63 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 248 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 63 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 248
  (Polychromatic418967fa.accept_17_2_12_10_1_9034 2 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 248 (accept_3_2 1 63 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 248 (allA_succ_of_accept 61 62 248
  (accept_3_2 61 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 248 2 30 31 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 248
  (Polychromatic418967fa.accept_12_11_2_8_1_511 59 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 248 2 29 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 62 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 248 2 28 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 248 (accept_3_2 55 62 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 248 2 27 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 53
  62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 248 2 26 31 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 248 2 25 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 248 (accept_3_2 49 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 248 2 24 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 62 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 248 2 23 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 248 2 22 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 248 (accept_3_2 43 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 248 2 21 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 62 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 248 2 20 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 248 2 19 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 248 (accept_3_2 37 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 248 2 18 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 62 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 248 2 17 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 248
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 248 2 16 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 31 62 248 31 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 62 248 2 15 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 62 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 248 2 14 31 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 248
  (Polychromatic418967fa.accept_25_2_12_23_1_13311 27 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 62 248 2 13 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 62 248 (accept_3_2 25 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 248 2 12 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 62 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 248 2 11 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 248
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 248 2 10 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 248 (accept_3_2 19 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 248 2 9 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 62 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 248 2 8 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 248 2 7 31 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 248 (accept_3_2 13
  62 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 248 2 6 31 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 62 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 248 2 5 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 62 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 248 2 4 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 248 (accept_3_2 7 62 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 248 2 3 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 62 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 248 2 2 31 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 62
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 248 2 1 31 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 248 (accept_3_2 1 62
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 248 (allA_of_3_0 61 61 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 248 (allA_succ_of_accept 59 60 248
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 248 2 29 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 248 4 14 15 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 248 (accept_3_2 55 60 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 248 2 27 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 53
  60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 248 4 13 15 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 248
  (Polychromatic418967fa.accept_13_12_8_1_1_825 51 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 248 2 25 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 60 248 (accept_3_2 49 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 248 4 12 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 60 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 248 2 23 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 248 (Polychromatic418967fa.accept_11_1_5_6_1_397 45
  60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 248 4 11 15 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 248 (accept_3_2 43
  60 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 248 2 21 30 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 248 4 10 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 248 2 19 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 248 (accept_3_2 37 60 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 248 4 9 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 60 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 248 2 17 30 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 248
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 248 4 8 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 248 (accept_3_2 31 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  248 2 15 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 60 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 248 4 7 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 248 2 13 30 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 248 (accept_3_2 25 60 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 248 4 6 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 248 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 60 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 248 2 11 30 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 248 4 5 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 248 (accept_3_2 19 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  248 2 9 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 248 4 4 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 248 2 7 30 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 248 (accept_3_2 13 60 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 248 4 3 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 248 2 5 30 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 248
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 248 4 2 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 248 (accept_3_2 7 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 248
  2 3 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  248 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 60 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 60 248 4 1 15 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 60 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 248 2 1 30 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 248 (accept_3_2 1 60 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 60 248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 248
  (allA_succ_of_accept 58 59 248 (accept_3_2 58 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 248 (Polychromatic418967fa.accept_19_18_2_1_1_5375 56 59 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 248 (accept_3_2 55 59 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 59 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 248
  (Polychromatic418967fa.accept_16_5_11_8_1_3431 53 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 248 (accept_3_2 52 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 248 (accept_3_2 49 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 248 (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 59 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 248
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 248 (accept_3_2 46 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 248 (accept_3_2 43 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 248 (Polychromatic418967fa.accept_13_3_7_1_1_334 42 59 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 248
  (Polychromatic418967fa.accept_10_1_9_8_1_123 41 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 248 (accept_3_2 40 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 248 (accept_3_2 37 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 248 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 59 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 248
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 248 (accept_3_2 34 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 248 (Polychromatic418967fa.accept_13_6_7_1_1_335 32 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 248 (accept_3_2 31 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 248 (Polychromatic418967fa.accept_22_8_15_6_1_8810 30 59 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 248
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 248 (accept_3_2 28 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 248 (accept_3_2 25 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 59 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 248
  (Polychromatic418967fa.accept_26_23_7_14_1_14999 23 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 59 248 (accept_3_2 22 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 59 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 248 (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 59
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 248 (accept_3_2 19 59 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 248 (Polychromatic418967fa.accept_19_18_2_1_1_5375
  18 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 248
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 248 (accept_3_2 16 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 248 (accept_3_2 13 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 248 (Polychromatic418967fa.accept_16_12_11_8_1_832 12 59 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 248
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 248 (accept_3_2 10 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 248 (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 248 (accept_3_2 7 59 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 248 (Polychromatic418967fa.accept_13_6_7_1_1_335 6 59 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 248
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 248 (accept_3_2 4 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 248 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 59 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 248 (accept_3_2 1 59 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 248))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 248 (allA_of_3_0
  58 58 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 248 (allA_succ_of_accept 56 57 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 248 (accept_3_2 55 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 248 (accept_3_2 52 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 57 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 248
  (Polychromatic418967fa.accept_15_5_12_8_1_3168 50 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 248 (accept_3_2 49 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 248 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 248 (accept_3_2 46 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 57 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 248 (accept_3_2 43 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 248 (accept_3_2 40 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 57 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 248 (accept_3_2 37 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 248 (Polychromatic418967fa.accept_16_4_9_8_1_2509 36 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 248 (accept_3_2 34 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 248 (accept_3_2 31 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 248 (accept_3_2 28 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 248 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 57 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 248 (accept_3_2 25 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 248 (accept_3_2 22 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 248 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 57 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 248 (accept_3_2 19 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 248 (accept_3_2 16 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 248
  (Polychromatic418967fa.accept_21_14_15_17_1_2972 14 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 57 248 (accept_3_2 13 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 248 (accept_3_2 10 57 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 9
  57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 248
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 248 (accept_3_2 7 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  248 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 248 (accept_3_2 4 57 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 248 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 57 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  57 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 248 (accept_3_2 1 57 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 248 (allA_succ_of_accept 55 56 248 (accept_3_2 55 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 248 2 27 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 56 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 248 4 13 14 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 56 248 2 25 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 56 248 (accept_3_2 49 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 56 248 8 6 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 56 248 (Polychromatic418967fa.accept_17_13_5_10_1_2839 47 56 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 248 2 23 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 248 (Polychromatic418967fa.accept_19_7_18_1_1_1662
  45 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 248 4 11 14 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 248 (accept_3_2 43
  56 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 248 2 21 28 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 248
  (Polychromatic418967fa.accept_21_20_14_17_1_10643 41 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 56 248 8 5 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 56 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 56 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 248 2 19 28 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 248 (accept_3_2 37 56 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 248 4 9 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 56 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 248 2 17 28 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 248 8 4 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 248 (accept_3_2 31 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  248 2 15 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 56 248 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 248 4 7 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 248 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 56 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 248 2 13 28 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 248 (accept_3_2 25 56 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 248 8 3 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 56 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 248 2 11 28 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 248 4 5 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 248 (accept_3_2 19 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  248 2 9 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 248 8 2 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 56 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 248 2 7 28 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 248 (accept_3_2 13 56 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 248 4 3 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 248 (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 56
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 248 2 5 28 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 248
  (Polychromatic418967fa.accept_21_9_14_17_1_12039 9 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 248 8 1 7 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 248 (accept_3_2 7 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 248
  2 3 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  248 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 56 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 248 4 1 14 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 248 2 1 28 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 248 (accept_3_2 1 56 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 248)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 248 (allA_of_3_0 55
  55 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 248 (allA_succ_of_accept 53 54 248
  (Polychromatic418967fa.accept_19_15_16_1_1_11087 53 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 54 248 2 26 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 54 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 54 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 248 2 25 27 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 248 (accept_3_2 49 54 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 248 2 24 27 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 248
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 248 2 23 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 54 248 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 54 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 248 2 22 27 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 248 (accept_3_2 43 54 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 248 2 21 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 248 (Polychromatic418967fa.accept_17_7_3_10_1_2881
  41 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 248 2 20 27 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 248
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 248 2 19 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 54 248 (accept_3_2 37 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 248 2 18 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 248 (Polychromatic418967fa.accept_13_9_2_1_1_813 35 54 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 248 2 17 27 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 248 2 16 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 54 248 (accept_3_2 31 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 248 2 15 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 54 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 248 2 14 27 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 248
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 248 2 13 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 248 (accept_3_2 25 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 248 2 12 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 54 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 248 2 11 27 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 248 2 10 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 248 (accept_3_2 19 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 248 2 9 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 248 (Polychromatic418967fa.accept_15_2_9_8_1_736 17 54 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 248 2 8 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 248 2 7 27 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 248 (accept_3_2 13
  54 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 248 2 6 27 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 248
  (Polychromatic418967fa.accept_17_11_3_10_1_2838 11 54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 248 2 5 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 248 2 4 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 248 (accept_3_2 7 54 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 248 2 3 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 248 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 54 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 248 2 2 27 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 248 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  54 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 248 2 1 27 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 248 (accept_3_2 1 54
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 248))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 248 (allA_succ_of_accept 52 53 248 (accept_3_2 52 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 53 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 248 (accept_3_2 49 53 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 48
  53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 248 (accept_3_2 46 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 248 (Polychromatic418967fa.accept_16_12_5_8_1_2492 44 53 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 248 (accept_3_2 43 53 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 248 (accept_3_2 40 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 248 (accept_3_2 37 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 248
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 248 (accept_3_2 34 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 248 (Polychromatic418967fa.accept_17_15_2_10_1_9021 32 53 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 248 (accept_3_2 31 53 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 248 (accept_3_2 28 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 248 (accept_3_2 25 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 248
  (Polychromatic418967fa.accept_19_4_15_1_1_2819 23 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 248 (accept_3_2 22 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 248 (accept_3_2 19 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 248 (Polychromatic418967fa.accept_20_18_13_8_1_9398 18 53 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 248
  (Polychromatic418967fa.accept_19_17_15_1_1_8300 17 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 248 (accept_3_2 16 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 248 (Polychromatic418967fa.accept_11_3_9_6_1_105 14 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 248 (accept_3_2 13 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 53 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 248 (accept_3_2 10 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 248 (accept_3_2 7 53 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 248
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 248 (accept_3_2 4 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 53 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 248 (accept_3_2 1 53 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 248))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 248 (allA_of_3_0 52 52
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 248 (allA_succ_of_accept 50 51 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 248 (accept_3_2 49 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 248 (accept_3_2 46 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 248 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 51 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 248 (accept_3_2 43 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 248 (accept_3_2 40 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 51 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 248 (accept_3_2 37 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 248 (accept_3_2 34 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 248
  (Polychromatic418967fa.accept_15_2_6_8_1_754 32 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 248 (accept_3_2 31 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 248 (accept_3_2 28 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 248 (accept_3_2 25 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 248 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 248 (accept_3_2 22 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 248 (accept_3_2 19 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 248 (accept_3_2 16 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 248
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 248 (accept_3_2 13 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 248 (accept_3_2 10 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 248 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 51 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 248 (accept_3_2 7 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  248 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 248 (accept_3_2 4 51 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  51 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 248 (accept_3_2 1 51 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 248)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 248 (allA_succ_of_accept 49 50 248 (accept_3_2 49 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 248 2 24 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 50 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 50 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 248 2 23 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 248
  (Polychromatic418967fa.accept_19_7_12_1_1_6830 45 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 50 248 2 22 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 50 248 (accept_3_2 43 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 50 248 2 21 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 50 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 248 2 20 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 248 2 19 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 50 248 (accept_3_2 37 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 248 2 18 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 50 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 248 2 17 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 248 2 16 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 248 (accept_3_2 31 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 248 2 15 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 248 2 14 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 248
  (Polychromatic418967fa.accept_15_12_5_8_1_5247 27 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 248 2 13 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 248 (accept_3_2 25 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 248 2 12 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 50 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 248 2 11 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 248
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 248 2 10 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 248 (accept_3_2 19 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 248 2 9 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 50 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 248 2 8 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 248 (Polychromatic418967fa.accept_20_15_10_8_1_6398
  15 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 248 2 7 25 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 248 (accept_3_2 13
  50 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 248 2 6 25 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 50 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 248 2 5 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 50 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 248 2 4 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 248 (accept_3_2 7 50 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 248 2 3 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 50 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 248 2 2 25 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 248 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3
  50 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 248 2 1 25 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 248 (accept_3_2 1 50
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 248))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 248 (allA_of_3_0 49 49 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 248
  (allA_succ_of_accept 47 48 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 248 2 23 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 248 (Polychromatic418967fa.accept_13_6_9_1_1_5604
  45 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 248 4 11 12 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 248 (accept_3_2 43
  48 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 248 2 21 24 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 248
  (Polychromatic418967fa.accept_13_2_9_1_1_67 41 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 248 8 5 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 48 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 248 2 19 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 248 (accept_3_2 37 48 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 248 4 9 12 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 48 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 248 2 17 24 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 248
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 248 8 4 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 248 (accept_3_2 31 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  248 2 15 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 48 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 248 4 7 12 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 248 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 48 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 248 2 13 24 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 248 (accept_3_2 25 48 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 248 8 3 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 248 2 11 24 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 248
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 248 4 5 12 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 248 (accept_3_2 19 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  248 2 9 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 248 8 2 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 248 2 7 24 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 248 (accept_3_2 13 48 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 248 4 3 12 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 248 2 5 24 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 248 8 1 6 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 248 (accept_3_2 7 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 248
  2 3 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  248 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 48 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 248 4 1 12 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 248 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 48 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 248 2 1 24 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 248 (accept_3_2 1 48 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 48 248)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 248
  (allA_succ_of_accept 46 47 248 (accept_3_2 46 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 248 (accept_3_2 43 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 248
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 41 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 248 (accept_3_2 40 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 248 (accept_3_2 37 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 248 (accept_3_2 34 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 248 (Polychromatic418967fa.accept_13_6_8_1_1_2913 32 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 248 (accept_3_2 31 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 47 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 248 (accept_3_2 28 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 248 (accept_3_2 25 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 248 (accept_3_2 22 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 248 (Polychromatic418967fa.accept_11_9_3_6_1_797 20 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 248 (accept_3_2 19 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 248 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 47 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 248 (accept_3_2 16 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 248 (accept_3_2 13 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 248
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 248 (accept_3_2 10 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 248 (accept_3_2 7 47 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 248
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 248 (accept_3_2 4 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 47 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 248 (accept_3_2 1 47 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 248))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 248 (allA_of_3_0 46 46 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 248 (allA_succ_of_accept 44 45 248
  (Polychromatic418967fa.accept_13_5_6_1_1_822 44 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 248 (accept_3_2 43 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 248 (accept_3_2 40 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 248 (Polychromatic418967fa.accept_18_3_9_14_1_2219 39 45 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 248
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 248 (accept_3_2 37 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 248 (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 248 (accept_3_2 34 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 248 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 45 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 248
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 248 (accept_3_2 31 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 248 (accept_3_2 28 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 248 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 45 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 248
  (Polychromatic418967fa.accept_23_3_22_18_1_14998 26 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 45 248 (accept_3_2 25 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 45 248 (Polychromatic418967fa.accept_18_6_9_14_1_9915 24 45 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 248 (accept_3_2 22 45 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 248 (Polychromatic418967fa.accept_13_8_6_1_1_3808
  21 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 248
  (Polychromatic418967fa.accept_13_7_6_1_1_368 20 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 248 (accept_3_2 19 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 248 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 248 (accept_3_2 16 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 248 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 45 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 248
  (Polychromatic418967fa.accept_20_14_5_8_1_4870 14 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 248 (accept_3_2 13 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 248 (accept_3_2 10 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 248 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 45 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 248
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 248 (accept_3_2 7 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  248 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 248 (accept_3_2 4 45 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 248 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 45 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  45 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 248 (accept_3_2 1 45 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 248))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  248 (allA_succ_of_accept 43 44 248 (accept_3_2 43 44 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 248 2 21 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 44 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 248 4 10 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 39
  44 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 248 2 19 22 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 248 (accept_3_2 37
  44 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 248 4 9 11 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 248
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 44 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 248 2 17 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 44 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 44 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 248 4 8 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 248 (accept_3_2 31 44 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 248 2 15 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 44 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 248 4 7 11 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 248
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 44 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 248 2 13 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 248 (accept_3_2 25 44 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 248 4 6 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 44 248 (Polychromatic418967fa.accept_16_7_12_8_1_2450 23 44 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 248 2 11 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 21
  44 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 248 4 5 11 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 248 (accept_3_2 19
  44 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 248 2 9 22 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 248
  (Polychromatic418967fa.accept_13_4_5_1_1_833 17 44 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 44 248 4 4 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 44 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 44 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 248 2 7 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 248 (accept_3_2 13 44 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 248 4 3 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 248 2 5 22 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 248
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 44 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 248 4 2 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 248 (accept_3_2 7 44 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 248
  2 3 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  248 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 248 4 1 11 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 44 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 248 2 1 22 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 248 (accept_3_2 1 44 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 248)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 248 (allA_of_3_0 43 43 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 248 (allA_succ_of_accept 41 42 248
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 42 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 248 2 20 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 248 2 19 21 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 248 (accept_3_2 37 42 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 248 2 18 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 35
  42 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 248 2 17 21 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 248 2 16 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 248 (accept_3_2 31 42 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 248 2 15 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 248 2 14 21 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 248 2 13 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 248 (accept_3_2 25 42 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 248 2 12 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 248 (Polychromatic418967fa.accept_24_23_18_8_1_4564 23 42 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 248 2 11 21 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 248 2 10 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 42 248 (accept_3_2 19 42 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 248 2 9 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 248 2 8 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 15
  42 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 248 2 7 21 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 248 (accept_3_2 13
  42 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 248 2 6 21 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 248 2 5 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 248 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 248 2 4 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 248 (accept_3_2 7 42 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 42 248 2 3 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 42 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 42 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 248 2 2 21 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 248 2 1 21 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 248 (accept_3_2 1 42
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 248)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41
  248 (allA_succ_of_accept 40 41 248 (accept_3_2 40 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 41 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 248 (accept_3_2 37 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 248 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 41 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 248
  (Polychromatic418967fa.accept_13_9_2_1_1_813 35 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 248 (accept_3_2 34 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 248 (accept_3_2 31 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 41 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 248
  (Polychromatic418967fa.accept_10_9_1_8_1_755 29 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 248 (accept_3_2 28 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 248 (accept_3_2 25 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 248 (Polychromatic418967fa.accept_19_5_3_1_1_4055 24 41 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 248 (accept_3_2 22 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 248 (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 41 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 248 (accept_3_2 19 41 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 248
  (Polychromatic418967fa.accept_14_3_13_10_1_761 17 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 248 (accept_3_2 16 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 248 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 248 (accept_3_2 13 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 248 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 41 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 248 (accept_3_2 10 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 248 (Polychromatic418967fa.accept_18_8_5_14_1_3353 8 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 248 (accept_3_2 7 41 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 248 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 41 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 248
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 248 (accept_3_2 4 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 41 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 248 (accept_3_2 1 41 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 248))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 248 (allA_of_3_0 40 40 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 248 (allA_succ_of_accept 38 39 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 248 (accept_3_2 37 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 248 (accept_3_2 34 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 39 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 248
  (Polychromatic418967fa.accept_15_2_9_8_1_736 32 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 248 (accept_3_2 31 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 248 (accept_3_2 28 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 248
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 248 (accept_3_2 25 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 248 (accept_3_2 22 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 248 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 39 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 248 (accept_3_2 19 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 248 (accept_3_2 16 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 248
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 248 (accept_3_2 13 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 248 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 248 (accept_3_2 10 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 248 (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 39 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 248 (accept_3_2 7 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  248 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 248 (accept_3_2 4 39 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 248 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 39 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 39
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 248 (accept_3_2 1 39 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 248))))))))))))))))))))))))))))))))))))))) (allB_succ 38 248
  (allA_succ_of_accept 37 38 248 (accept_3_2 37 38 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  248 2 18 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 248 2 17 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 38 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 248 2 16 19 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 248 (accept_3_2 31 38 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 248 2 15 19 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 248
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 38 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 248 2 14 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 248 (Polychromatic418967fa.accept_25_2_13_23_1_14997 27 38 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 248 2 13 19 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 248 (accept_3_2 25 38 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 248 2 12 19 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 248
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 38 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 38 248 2 11 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 38 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 38 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 248 2 10 19 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 248 (accept_3_2 19 38 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38 248 2 9 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 38 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 17
  38 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 248 2 8 19 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 38 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 38 248 2 7 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 38 248 (accept_3_2 13 38 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38
  248 2 6 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  38 248 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 38 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 38 248 2 5 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 38 248 (Polychromatic418967fa.accept_22_9_16_6_1_2493 9 38 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 248 2 4 19 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 248 (accept_3_2 7 38 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 248 2 3 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 38 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 248 2 2 19 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 38 248 2 1 19 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 38 248 (accept_3_2 1 38 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  248)))))))))))))))))))))))))))))))))))))) (allB_succ 37 248 (allA_of_3_0 37 37 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 248 (allA_succ_of_accept 35 36 248 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 36 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 248 2 17 18 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 248 4 8 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 248 (accept_3_2 31 36 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36
  248 2 15 18 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 36 248 (Polychromatic418967fa.accept_15_14_6_8_1_1410 29 36 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 36 248 4 7 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 36 248 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 36 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 248 2 13 18 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 248 (accept_3_2 25 36 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 248 4 6 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 248 2 11 18 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 248
  (Polychromatic418967fa.accept_16_5_4_8_1_1560 21 36 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 36 248 4 5 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 36 248 (accept_3_2 19 36 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36
  248 2 9 18 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  36 248 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 36 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 36 248 4 4 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 36 248 (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 36 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 248 2 7 18 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 248 (accept_3_2 13 36 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 248 4 3 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 248 2 5 18 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 248 4 2 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 248 (accept_3_2 7 36 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 248
  2 3 18 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36
  248 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 248 4 1 9 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 36 248 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 36 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 248 2 1 18 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 248 (accept_3_2 1 36 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 248)))))))))))))))))))))))))))))))))))) (allB_succ 35 248 (allA_succ_of_accept 34 35 248
  (accept_3_2 34 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 35 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 248 (accept_3_2 31 35 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 248 (accept_3_2 28 35
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 248 (Polychromatic418967fa.accept_6_3_5_2_1_12
  27 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 248
  (Polychromatic418967fa.accept_11_4_2_6_1_389 26 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 248 (accept_3_2 25 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 248 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 248 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 35 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 248 (accept_3_2 22 35 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 248 (accept_3_2 19 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 248 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 248 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 35 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 248 (accept_3_2 16 35 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 248
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 248 (accept_3_2 13 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 248 (accept_3_2 10 35 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 248
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 248 (accept_3_2 7 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  248 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 248 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 35 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 248 (accept_3_2 4 35 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  35 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 248 (accept_3_2 1 35 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 248))))))))))))))))))))))))))))))))))) (allB_succ 34 248
  (allA_of_3_0 34 34 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 248 (allA_succ_of_accept 32 33 248
  (Polychromatic418967fa.accept_13_6_7_1_1_335 32 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 248 (accept_3_2 31 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 248 (accept_3_2 28 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 248 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 33 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 248 (accept_3_2 25 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 248 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 248 (accept_3_2 22 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 248
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 248 (accept_3_2 19 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 248 (accept_3_2 16 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 248
  (Polychromatic418967fa.accept_20_14_13_8_1_4847 14 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 248 (accept_3_2 13 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 248 (accept_3_2 10 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 248 (accept_3_2 7 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  248 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 33 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 248 (accept_3_2 4 33 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 248 (accept_3_2 1 33 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  248))))))))))))))))))))))))))))))))) (allB_succ 32 248 (allA_succ_of_accept 31 32 248 (accept_3_2 31 32 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 248 2 15 16 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 29
  32 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 248 4 7 8 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 248
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 32 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 32 248 2 13 16 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 32 248 (accept_3_2 25 32 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 32 248 8 3 4 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 32 248 (Polychromatic418967fa.accept_21_2_11_17_1_4395 23 32 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 248 2 11 16 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 248 (Polychromatic418967fa.accept_13_8_6_1_1_3808
  21 32 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 248 4 5 8 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 248 (accept_3_2 19
  32 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 248 2 9 16 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32 248
  (Polychromatic418967fa.accept_22_17_10_6_1_5408 17 32 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 32 248 8 2 4 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 32 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 248 2 7 16 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 248 (accept_3_2 13 32 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 248 4 3 8 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 248 (Polychromatic418967fa.accept_28_11_4_24_1_14996 11 32 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 248 2 5 16 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 248
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 32 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 248 8 1 4 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 248 (accept_3_2 7 32 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 248
  2 3 16 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  248 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 32 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 248 4 1 8 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 248 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 32 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 248 2 1 16 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 248 (accept_3_2 1 32 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 248)))))))))))))))))))))))))))))))) (allB_succ 31 248 (allA_of_3_0 31 31 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 248 (allA_succ_of_accept 29 30 248
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 248 2 14 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 30 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 248 2 13 15 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 248 (accept_3_2 25 30 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 248 2 12 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 248 (Polychromatic418967fa.accept_13_10_4_1_1_2142
  23 30 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 248 2 11 15 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 248
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 248 2 10 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 248 (accept_3_2 19 30 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 248 2 9 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 30 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 248 2 8 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  30 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 248 2 7 15 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 248 (accept_3_2 13
  30 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 248 2 6 15 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 248 2 5 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 248 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 248 2 4 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 248 (accept_3_2 7 30 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 248 2 3 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 30 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 248 2 2 15 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 248 (Polychromatic418967fa.accept_11_3_8_6_1_788 3
  30 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 248 2 1 15 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 248 (accept_3_2 1 30
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 248)))))))))))))))))))))))))))))) (allB_succ 29 248
  (allA_succ_of_accept 28 29 248 (accept_3_2 28 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 29 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 248 (accept_3_2 25 29 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 29 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 248 (accept_3_2 22 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 248 (Polychromatic418967fa.accept_13_7_3_1_1_814 20 29 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 248 (accept_3_2 19 29 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 29 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 248 (accept_3_2 16 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 29 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 248 (accept_3_2 13 29 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 248
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 248 (accept_3_2 10 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 248 (accept_3_2 7 29 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 29 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 248
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 248 (accept_3_2 4 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 29 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 248 (accept_3_2 1 29 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 248))))))))))))))))))))))))))))) (allB_succ 28 248 (allA_of_3_0 28 28 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 248 (allA_succ_of_accept 26 27 248 (Polychromatic418967fa.accept_15_11_12_8_1_739
  26 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 248 (accept_3_2 25
  27 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 248
  (Polychromatic418967fa.accept_18_6_9_14_1_9915 24 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 248 (accept_3_2 22 27 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 248 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 27 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 248
  (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 248 (accept_3_2 19 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 248 (accept_3_2 16 27 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 27 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 248
  (Polychromatic418967fa.accept_23_14_4_18_1_5040 14 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 248 (accept_3_2 13 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 248 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 248 (accept_3_2 10 27 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 248
  (Polychromatic418967fa.accept_23_8_4_18_1_6756 8 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 248 (accept_3_2 7 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  248 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 248 (accept_3_2 4 27 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 248 (Polychromatic418967fa.accept_14_3_13_10_1_761 3 27 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  27 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 248 (accept_3_2 1 27 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 248))))))))))))))))))))))))))) (allB_succ 26 248
  (allA_succ_of_accept 25 26 248 (accept_3_2 25 26 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  248 2 12 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 26 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 248 2 11 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 248 2 10 13 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 248 (accept_3_2 19 26 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 248 2 9 13 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 248
  (Polychromatic418967fa.accept_12_5_2_8_1_172 17 26 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 26 248 2 8 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 26 248 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 26 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 248 2 7 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 248 (accept_3_2 13 26 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 248 2 6 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 26 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 248 2 5 13 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 26 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 248 2 4 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 248 (accept_3_2 7 26 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 248
  2 3 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  248 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 26 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 26 248 2 2 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 26 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 26 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 248 2 1 13 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 248 (accept_3_2 1 26 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 248)))))))))))))))))))))))))) (allB_succ 25 248 (allA_of_3_0 25 25 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 248 (allA_succ_of_accept 23 24 248 (Polychromatic418967fa.accept_13_10_11_1_1_2152
  23 24 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 248 2 11 12 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 248 4 5 6 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 248 (accept_3_2 19 24 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  248 2 9 12 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 248 8 2 3 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 248 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 24 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 248 2 7 12 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 248 (accept_3_2 13 24 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 248 4 3 6 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 248 2 5 12 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 248
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 24 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 248 8 1 3 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 248 (accept_3_2 7 24 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 248
  2 3 12 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  248 (Polychromatic418967fa.accept_25_5_24_23_1_14995 5 24 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 248 4 1 6 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 248 2 1 12 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 248 (accept_3_2 1 24 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 24 248)))))))))))))))))))))))) (allB_succ 23 248 (allA_succ_of_accept 22 23 248
  (accept_3_2 22 23 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 248 (accept_3_2 19 23 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 248 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 23 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 248 (Polychromatic418967fa.accept_13_4_10_1_1_1390
  17 23 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 248 (accept_3_2 16
  23 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 248 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 248 (accept_3_2 13 23 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 248 (Polychromatic418967fa.accept_10_1_3_8_1_136
  11 23 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 248 (accept_3_2 10
  23 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 248 (accept_3_2 7 23 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 5
  23 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 248 (accept_3_2 4 23 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 248
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 23 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 248 (accept_3_2 1 23 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  248))))))))))))))))))))))) (allB_succ 22 248 (allA_of_3_0 22 22 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 21 248 (allA_succ_of_accept 20 21 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 248 (accept_3_2 19 21 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 248 (accept_3_2 16 21 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 248 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 21 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 248 (accept_3_2 13 21 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 248 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 21 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 248 (accept_3_2 10 21 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 248 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 21 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 248 (accept_3_2 7 21 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 248 (accept_3_2 4 21 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  248 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 21 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 248 (accept_3_2 1 21 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 21 248))))))))))))))))))))) (allB_succ 20 248 (allA_succ_of_accept 19 20 248 (accept_3_2 19 20
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 248 2 9 10 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 248
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 248 4 4 5 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 248 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 20 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 248 2 7 10 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 248 (accept_3_2 13 20 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 248 4 3 5 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 248 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 248 2 5 10 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 248
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 248 4 2 5 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 248 (accept_3_2 7 20 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 248
  2 3 10 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  248 (Polychromatic418967fa.accept_16_5_4_8_1_1560 5 20 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 20 248 4 1 5 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 20 248 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 20 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 248 2 1 10 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 248 (accept_3_2 1 20 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 20 248)))))))))))))))))))) (allB_succ 19 248 (allA_of_3_0 19 19 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 18 248 (allA_succ_of_accept 17 18 248 (Polychromatic418967fa.accept_13_4_5_1_1_833 17
  18 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 248 2 8 9 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 18 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 248 2 7 9 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 248 (accept_3_2 13 18 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  248 2 6 9 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 248 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 18 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 248 2 5 9 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 248 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 18 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 248 2 4 9 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 248 (accept_3_2 7 18 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 248 2 3 9 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 248 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 18 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 248 2 2 9 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 18 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 248 2 1 9 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 248 (accept_3_2 1 18 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  248)))))))))))))))))) (allB_succ 17 248 (allA_succ_of_accept 16 17 248 (accept_3_2 16 17 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 248
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 17 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 248 (accept_3_2 13 17 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 17 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 248 (accept_3_2 10 17 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 248
  (Polychromatic418967fa.accept_22_8_17_6_1_8769 8 17 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 248 (accept_3_2 7 17 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  248 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 17 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 17 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 248 (accept_3_2 4 17 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  17 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 248 (accept_3_2 1 17 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 248))))))))))))))))) (allB_succ 16 248 (allA_of_3_0 16 16 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 248 (allA_succ_of_accept 14 15 248
  (Polychromatic418967fa.accept_19_14_15_1_1_6806 14 15 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 248 (accept_3_2 13 15 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 248 (accept_3_2 10 15 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 248
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 248 (accept_3_2 7 15 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  248 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 15 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 248 (accept_3_2 4 15 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 15 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  15 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 248 (accept_3_2 1 15 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 248))))))))))))))) (allB_succ 14 248 (allA_succ_of_accept 13 14
  248 (accept_3_2 13 14 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 248 2 6 7 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 248
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 248 2 5 7 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 248 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 14 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 248 2 4 7 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 248 (accept_3_2 7 14 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 248 2 3 7 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 248 2 2 7 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 248 (Polychromatic418967fa.accept_20_3_14_8_1_12152
  3 14 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 248 2 1 7 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 248 (accept_3_2 1 14
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 248)))))))))))))) (allB_succ 13 248 (allA_of_3_0 13 13 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 248 (allA_succ_of_accept 11 12 248
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 12 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 248 2 5 6 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 248 4 2 3 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 248 (accept_3_2 7 12 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 248 2 3 6 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 12 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 248 4 1 3 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 248 (Polychromatic418967fa.accept_15_3_12_8_1_738 3
  12 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 248 2 1 6 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 248 (accept_3_2 1 12
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 248)))))))))))) (allB_succ 11 248 (allA_succ_of_accept 10 11
  248 (accept_3_2 10 11 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 248 (accept_3_2 7 11 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 11 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 248 (Polychromatic418967fa.accept_15_5_11_8_1_1391
  5 11 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 248 (accept_3_2 4 11
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 248 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 11 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 248
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 11 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 248 (accept_3_2 1 11 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  248))))))))))) (allB_succ 10 248 (allA_of_3_0 10 10 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 248
  (allA_succ_of_accept 8 9 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 9 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 248 (accept_3_2 7 9 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 248 (accept_3_2 4 9 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 248 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 9
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 248
  (Polychromatic418967fa.accept_13_2_9_1_1_67 2 9 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 248 (accept_3_2 1 9 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 248)))))))))
  (allB_succ 8 248 (allA_succ_of_accept 7 8 248 (accept_3_2 7 8 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 248 2 3 4 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 248 4 1 2 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 8 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 248 2 1 4 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 248 (accept_3_2 1 8 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 248)))))))) (allB_succ 7 248 (allA_of_3_0 7 7 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 248 (allA_succ_of_accept 5 6 248 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 6
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 248 2 2 3 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 6 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 248 2 1 3 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 248 (accept_3_2 1 6 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 248))))))
  (allB_succ 5 248 (allA_succ_of_accept 4 5 248 (accept_3_2 4 5 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 5 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 248 (accept_3_2 1 5 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 248))))) (allB_succ 4 248 (allA_of_3_0 4 4 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 248 (allA_succ_of_accept 2 3 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 3 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 248 (accept_3_2 1 3 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 248))) (allB_succ 2 248 (allA_succ_of_accept 1 2 248 (accept_3_2 1 2 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 248)) (allB_two
  248)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


