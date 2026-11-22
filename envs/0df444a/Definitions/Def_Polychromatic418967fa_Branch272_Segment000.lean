-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch272_Segment000
-- name    : Polychromatic418967fa_Branch272_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:49:34.392377+00:00
-- url     : https://prove2.me/theorems/08e1c9c6-6595-471d-ad18-ab5da2570952
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

def Polychromatic418967fa.branch_272_segment_000 : allB 123 272 :=
  allB_succ 122 272 (allA_succ_of_accept 121 122 272 (accept_3_2 121 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 122 272 2 60 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 122 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 119 122 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 122 272 2 59 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 122 272
  (Polychromatic418967fa.accept_19_3_8_6_1_4368 117 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 122 272 2 58 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 122 272 (accept_3_2 115 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 122 272 2 57 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 122 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 113 122 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 122 272 2 56 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 122 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 111 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 122 272 2 55 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 122 272 (accept_3_2 109 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 122 272 2 54 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 122 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 107 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 272 2 53 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 105 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 272 2 52 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 272 (accept_3_2 103 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 272 2 51 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 101 122 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 272 2 50 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 272
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 99 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 272 2 49 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 272 (accept_3_2 97 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 272 2 48 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 95 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 272 2 47 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 93 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 272 2 46 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 272 (accept_3_2 91 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 272 2 45 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 272 2 44 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 272 2 43 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 272 (accept_3_2 85 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 272 2 42 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 122 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 272 2 41 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 272 2 40 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 272 (accept_3_2 79 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 272 2 39 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 272 2 38 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 272 2 37 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 272 (accept_3_2 73 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 272 2 36 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 272 2 35 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 272 2 34 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 272 (accept_3_2 67 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 272 2 33 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 272 2 32 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 272
  (Polychromatic418967fa.accept_24_15_2_8_1_11685 63 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 122 272 2 31 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 122 272 (accept_3_2 61 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 272 2 30 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 59 122 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 272 2 29 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 272 2 28 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 272 (accept_3_2 55 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 272 2 27 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 272 2 26 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 272 2 25 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 272 (accept_3_2 49 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 272 2 24 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 122 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 272 2 23 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 272
  (Polychromatic418967fa.accept_13_6_5_12_1_307 45 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 272 2 22 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 272 (accept_3_2 43 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 272 2 21 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 272 2 20 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 272 2 19 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 272 (accept_3_2 37 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 272 2 18 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 272 2 17 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 272 2 16 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 272 (accept_3_2 31 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 272 2 15 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 272 2 14 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 272
  (Polychromatic418967fa.accept_13_1_5_12_1_306 27 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 272 2 13 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 272 (accept_3_2 25 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 272 2 12 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 272 2 11 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 272 2 10 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 272 (accept_3_2 19 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 272 2 9 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 272 2 8 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 272 2 7 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 272 (accept_3_2 13 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 272 2 6 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 122 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 272 2 5 61 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 272 2 4 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 272 (accept_3_2 7 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  272 2 3 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 122 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 272 2 2 61 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 122 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 272 2 1 61 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 272 (accept_3_2 1 122 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 272 (allA_of_3_0 121 121 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 272
  (allA_succ_of_accept 119 120 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 119 120 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 120 272 2 59 60 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 120 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 117 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 120 272 4 29 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 120 272 (accept_3_2 115 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 120 272 2 57 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 120 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 113 120 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 120 272 8 14 15 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 120 272
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 111 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 120 272 2 55 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 120 272 (accept_3_2 109 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 120 272 4 27 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 120 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 107 120 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 120 272 2 53 60 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 120 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 105 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 120 272 8 13 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 120 272 (accept_3_2 103 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 120 272 2 51 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 120 272 (Polychromatic418967fa.accept_23_9_5_19_1_16682 101 120 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 272 4 25 30 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 120 272
  (Polychromatic418967fa.accept_22_11_10_8_1_9010 99 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 120 272 2 49 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 120 272 (accept_3_2 97 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 272 8 12 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 120 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 95 120 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 120 272 2 47 60 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 120 272 4 23 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 120 272 (accept_3_2 91 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 272 2 45 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 120 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 272 8 11 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 120 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 87 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 120 272 2 43 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 120 272 (accept_3_2 85 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 272 4 21 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 272 (Polychromatic418967fa.accept_23_14_5_19_1_11850 83 120 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 272 2 41 60 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 272
  (Polychromatic418967fa.accept_21_18_15_20_1_6076 81 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 120 272 8 10 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 120 272 (accept_3_2 79 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 272 2 39 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 120 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 272 4 19 30 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 120 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 120 272 2 37 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 120 272 (accept_3_2 73 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 272 8 9 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 120 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 120 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 272 2 35 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69
  120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 272 4 17 30 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 272 (accept_3_2 67
  120 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 272 2 33 60 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 120 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 120 272 8 8 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 120 272 (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 120 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 120 272 2 31 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 272 (accept_3_2 61 120 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 272 4 15 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 120 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 272 2 29 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 272
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 57 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 272 8 7 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 120 272 (accept_3_2 55 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  120 272 2 27 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 120 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 120 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 272 4 13 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 51
  120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 272 2 25 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 272 (accept_3_2 49
  120 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 272 8 6 15 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 272 2 23 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 120 272 (Polychromatic418967fa.accept_27_18_12_2_1_16681 45 120 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 120 272 4 11 30 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 272 (accept_3_2 43 120 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 272 2 21 60 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 272 8 5 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 120 272 (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 120 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 272 2 19 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 272 (accept_3_2 37 120 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 272 4 9 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 120 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 120 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 272 2 17 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 272 8 4 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 120 272 (accept_3_2 31 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  120 272 2 15 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 272 (Polychromatic418967fa.accept_22_7_10_8_1_9009 29 120 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 272 4 7 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 272
  (Polychromatic418967fa.accept_21_6_15_20_1_12224 27 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 120 272 2 13 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 120 272 (accept_3_2 25 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 272 8 3 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 120 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 272 2 11 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 272 (Polychromatic418967fa.accept_14_7_8_6_1_1164
  21 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 272 4 5 30 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 272
  (accept_3_2 19 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 272 2 9 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 272 8 2 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 120 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 120 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 272 2 7 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 272 (accept_3_2 13 120 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 272 4 3 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 272 (Polychromatic418967fa.accept_22_11_10_8_1_9010 11 120
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 272 2 5 60 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 272 8 1 15 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 272 (accept_3_2 7 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120
  272 2 3 60 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  120 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 120 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 272 4 1 30 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 120 272 (Polychromatic418967fa.accept_18_3_12_2_1_2639 3 120 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 272 2 1 60 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 272 (accept_3_2 1 120 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 272 (allA_succ_of_accept 118 119 272 (accept_3_2 118 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 272 (Polychromatic418967fa.accept_21_11_14_20_1_12235 116
  119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 272 (accept_3_2 115
  119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 272
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 114 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 119 272 (Polychromatic418967fa.accept_14_1_7_6_1_3604 113 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 272 (accept_3_2 112 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 110 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 272 (accept_3_2 109 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 272 (Polychromatic418967fa.accept_13_4_2_12_1_2800 108 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 107 119 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 272 (accept_3_2 106 119 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12
  105 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 272
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 104 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 119 272 (accept_3_2 103 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 119 272 17 6 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 119 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 101 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 272 (accept_3_2 100 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 119 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 119 272
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 98 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 119 272 (accept_3_2 97 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 119 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 96 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 119 272 (Polychromatic418967fa.accept_13_4_2_12_1_2800 95 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 272 (accept_3_2 94 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 119 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 119 272
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 92 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 119 272 (accept_3_2 91 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 119 272 (Polychromatic418967fa.accept_19_14_5_6_1_12685 90 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 119 272 (Polychromatic418967fa.accept_18_17_11_2_1_7782 89 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 119 272 (accept_3_2 88 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 119 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 86 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 119 272 17 5 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 119 272 (Polychromatic418967fa.accept_13_6_2_12_1_2802 84 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 83 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 119 272 (accept_3_2 82 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 119 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 81 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 119 272 (Polychromatic418967fa.accept_15_5_14_2_1_1876 80 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 272 (accept_3_2 79 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 119 272 (Polychromatic418967fa.accept_14_8_7_6_1_1159 78 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 272
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 77 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 119 272 (accept_3_2 76 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 119 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 272 (accept_3_2 73 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 272 (Polychromatic418967fa.accept_15_12_14_2_1_3794 72 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 272
  (Polychromatic418967fa.accept_10_1_9_2_1_45 71 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 119 272 (accept_3_2 70 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 119 272 17 4 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 119 272 (accept_3_2 67 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 119 272 (Polychromatic418967fa.accept_13_1_2_12_1_1299 66 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 65 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 272 (accept_3_2 64 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 119 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 272 (accept_3_2 61 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 119 272 (Polychromatic418967fa.accept_19_3_5_6_1_7135 60 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 272
  (Polychromatic418967fa.accept_21_17_14_20_1_7811 59 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 119 272 (accept_3_2 58 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 272 (Polychromatic418967fa.accept_13_4_2_12_1_2800 56 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 272 (accept_3_2 55 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 272
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 119 272 (Polychromatic418967fa.accept_13_1_2_12_1_1299 53 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 272 (accept_3_2 52 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 119 272 17 3 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 119 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 272 (accept_3_2 49 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 272 (Polychromatic418967fa.accept_15_3_14_2_1_1888 48 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 272
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 272 (accept_3_2 46 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 44 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 272 (accept_3_2 43 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 272 (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 272
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 272 (accept_3_2 40 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 272 (accept_3_2 37 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 272 (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 272
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 119 272 17 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 272 (accept_3_2 31 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 272
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 119 272 (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 272 (accept_3_2 28 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 272 (Polychromatic418967fa.accept_12_2_11_8_1_504
  26 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 272 (accept_3_2 25
  119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 272
  (Polychromatic418967fa.accept_23_1_4_19_1_10232 24 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 272 (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 272 (accept_3_2 22 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 272
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 272 (accept_3_2 19 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 17 119 272 17 1 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 16 119 272 (accept_3_2 16 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 272 (accept_3_2 13 119
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 272
  (Polychromatic418967fa.accept_15_12_14_2_1_3794 12 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 119 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 272 (accept_3_2 10 119 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 272
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 272 (accept_3_2 7 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 272 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 272 (accept_3_2 4 119 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 272 (accept_3_2 1 119 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 272 (allA_of_3_0 118 118 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 272
  (allA_succ_of_accept 116 117 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 116 117 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 272 (accept_3_2 115 117 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 114 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 272 (accept_3_2 112 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 272 (Polychromatic418967fa.accept_14_13_5_6_1_2747 111 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 272 (Polychromatic418967fa.accept_15_5_12_2_1_2820 110 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 272 (accept_3_2 109 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 272
  (Polychromatic418967fa.accept_15_3_12_2_1_507 108 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 107 117 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 117 272 (accept_3_2 106 117 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 117 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 105 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 272
  (Polychromatic418967fa.accept_10_4_7_2_1_211 104 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 117 272 (accept_3_2 103 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 117 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 102 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 117 272 (accept_3_2 100 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 117 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 272
  (Polychromatic418967fa.accept_22_10_7_8_1_16669 98 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 117 272 (accept_3_2 97 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 117 272 (Polychromatic418967fa.accept_15_6_12_2_1_2803 96 117 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 117 272 (accept_3_2 94 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 272 (Polychromatic418967fa.accept_15_3_12_2_1_507
  93 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 117 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 92 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 117 272 (accept_3_2 91 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 117 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 272 (accept_3_2 88 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 272 (Polychromatic418967fa.accept_20_7_17_12_1_11156 87 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 117 272
  (Polychromatic418967fa.accept_20_6_17_12_1_8210 86 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 117 272 (accept_3_2 85 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 117 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 117 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 272 (accept_3_2 82 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 117 272 (Polychromatic418967fa.accept_7_4_5_6_1_344
  81 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 272
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 80 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 117 272 (accept_3_2 79 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 117 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 272 (accept_3_2 76 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 117 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 75 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 74 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 272 (accept_3_2 73 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 117 272 (Polychromatic418967fa.accept_21_9_12_20_1_10792 72 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 272 (accept_3_2 70 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 69 117
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 117 272
  (Polychromatic418967fa.accept_23_22_2_19_1_13506 68 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 117 272 (accept_3_2 67 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 117 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 117 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 272 (accept_3_2 64 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 272 (Polychromatic418967fa.accept_15_3_12_2_1_507
  63 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 117 272
  (Polychromatic418967fa.accept_19_5_3_6_1_8642 62 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 272 (accept_3_2 61 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 117 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 272 (accept_3_2 58 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 117 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 272
  (Polychromatic418967fa.accept_19_18_3_6_1_9989 56 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 272 (accept_3_2 55 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 117 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 272 (accept_3_2 52 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 272 (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 272 (accept_3_2 49 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 117 272 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 272 (accept_3_2 46 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 272
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 272 (accept_3_2 43 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 272 (accept_3_2 40 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 272
  (Polychromatic418967fa.accept_22_16_7_8_1_15092 38 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 117 272 (accept_3_2 37 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 117 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 117 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 272 (accept_3_2 34 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 272 (Polychromatic418967fa.accept_15_3_12_2_1_507
  33 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 272 (accept_3_2 31 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 272 (accept_3_2 28 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 272 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 272
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 272 (accept_3_2 25 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 272 (accept_3_2 22 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 272 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 117 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 272
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 272 (accept_3_2 19 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 272 (accept_3_2 16 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 272
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 272 (accept_3_2 13 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 272 (Polychromatic418967fa.accept_22_12_7_8_1_8957 12 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 272 (accept_3_2 10 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 272 (accept_3_2 7 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 272 (accept_3_2 4 117 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 117 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 272
  (Polychromatic418967fa.accept_19_2_3_6_1_4415 2 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 272 (accept_3_2 1 117 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 272 (allA_succ_of_accept 115 116 272 (accept_3_2 115 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 272 2 57 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 113 116 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 272 4 28 29 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 111 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 116 272 2 55 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 116 272 (accept_3_2 109 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 272 4 27 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 107 116 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 272 2 53 58 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 105 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 116 272 4 26 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 116 272 (accept_3_2 103 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 272 2 51 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 101 116 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 272 4 25 29 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 272
  (Polychromatic418967fa.accept_15_9_11_2_1_1882 99 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 272 2 49 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 272 (accept_3_2 97 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 272 4 24 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 272 2 47 58 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 93 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 272 4 23 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 272 (accept_3_2 91 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 272 2 45 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 272 4 22 29 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 272 2 43 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 272 (accept_3_2 85 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 272 4 21 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 272 (Polychromatic418967fa.accept_22_17_6_8_1_13638 83 116 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 272 2 41 58 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 272 4 20 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 272 (accept_3_2 79 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 272 2 39 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 272 4 19 29 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 272 2 37 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 272 (accept_3_2 73 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 272 4 18 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 272 2 35 58 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 272 4 17 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 272 (accept_3_2 67 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 272 2 33 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 272 4 16 29 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 272
  (Polychromatic418967fa.accept_22_19_6_8_1_10580 63 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 116 272 2 31 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 116 272 (accept_3_2 61 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 272 4 15 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 272 2 29 58 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 272 4 14 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 272 (accept_3_2 55 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 272 2 27 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 272 (Polychromatic418967fa.accept_18_17_8_2_1_2622 53 116 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 272 4 13 29 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 272 2 25 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 272 (accept_3_2 49 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 272 4 12 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 272 2 23 58 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 272 4 11 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 272 (accept_3_2 43 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 272 2 21 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 272 4 10 29 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 272 2 19 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 272 (accept_3_2 37 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 272 4 9 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 272 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 116 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 272 2 17 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 33
  116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 272 4 8 29 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 272 (accept_3_2 31
  116 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 272 2 15 58 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 272
  (Polychromatic418967fa.accept_19_10_2_6_1_5731 29 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 272 4 7 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 272 (Polychromatic418967fa.accept_19_8_2_6_1_8677 27 116 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 272 2 13 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 272 (accept_3_2 25 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 272 4 6 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 116 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 272 2 11 58 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 272 4 5 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 272 (accept_3_2 19 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 272 2 9 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 116 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 272 4 4 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 272 2 7 58 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 272 (accept_3_2 13
  116 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 272 4 3 29 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 272 2 5 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 116 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 272 4 2 29 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 272 (accept_3_2 7 116 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 272 2 3 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 116 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 272 4 1 29 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 272 2 1 58 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 272 (accept_3_2 1 116 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 272 (allA_of_3_0 115 115 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 272
  (allA_succ_of_accept 113 114 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 113 114 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 272 2 56 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 114 272 (Polychromatic418967fa.accept_9_3_6_2_1_160
  111 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 272 2 55 57 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 272
  (accept_3_2 109 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 114 272 2 54 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 114 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 107 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 272 2 53 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 105 114 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 272 2 52 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 272 (accept_3_2 103 114 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 114 272 2 51 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 114 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 101 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 272 2 50 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 272 2 49 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 272 (accept_3_2 97 114 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 272 2 48 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 95
  114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 272 2 47 57 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 93 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 114 272 2 46 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 114 272 (accept_3_2 91 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 272 2 45 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 89 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 272 2 44 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 272 2 43 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 272 (accept_3_2 85 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 272 2 42 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 272 (Polychromatic418967fa.accept_15_8_9_2_1_1897 83 114 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 272 2 41 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 272 2 40 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 272 (accept_3_2 79 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 272 2 39 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 272 2 38 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 272 2 37 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 272 (accept_3_2 73 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 272 2 36 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 272 2 35 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 272 2 34 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 272 (accept_3_2 67 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 272 2 33 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 272 (Polychromatic418967fa.accept_21_2_9_20_1_9260 65 114 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 272 2 32 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 272 2 31 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 272 (accept_3_2 61 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 272 2 30 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 272 2 29 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 272 2 28 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 272 (accept_3_2 55 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 272 2 27 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 272 2 26 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 272
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 272 2 25 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 272 (accept_3_2 49 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 272 2 24 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 272 2 23 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 272 2 22 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 272 (accept_3_2 43 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 272 2 21 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 272 2 20 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 272 2 19 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 272 (accept_3_2 37 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 272 2 18 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 272 2 17 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 272 2 16 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 272 (accept_3_2 31 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 272 2 15 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 272 2 14 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 272 2 13 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 272 (accept_3_2 25 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 272 2 12 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 272 2 11 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 272 2 10 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 272 (accept_3_2 19 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 272 2 9 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 272 2 8 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 272 2 7 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 272 (accept_3_2 13 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 272 2 6 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 114 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 272 2 5 57 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 272 2 4 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 272 (accept_3_2 7 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  272 2 3 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 114 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 272 2 2 57 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 114 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 272 2 1 57 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 272 (accept_3_2 1 114 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 272 (allA_succ_of_accept 112 113 272 (accept_3_2 112 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 110 113
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 272 (accept_3_2 109 113
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 272
  (Polychromatic418967fa.accept_22_20_3_8_1_4033 108 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 113 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 107 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 272 (accept_3_2 106 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 113
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 272
  (Polychromatic418967fa.accept_11_5_3_8_1_454 104 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 272 (accept_3_2 103 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 101 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 272 (accept_3_2 100 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 113 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 98 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 272 (accept_3_2 97 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 95 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 272 (accept_3_2 94 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 272
  (Polychromatic418967fa.accept_27_11_5_2_1_16680 92 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 113 272 (accept_3_2 91 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 113 272 (Polychromatic418967fa.accept_20_10_13_12_1_9726 90 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 113 272 (Polychromatic418967fa.accept_7_5_1_6_1_163
  89 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 272 (accept_3_2 88
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 87 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 113 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 86 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 113 272 (accept_3_2 85 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 113 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 272 (Polychromatic418967fa.accept_11_6_3_8_1_843
  83 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 272 (accept_3_2 82
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 113 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 113 272 (accept_3_2 79 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 113 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 272 (Polychromatic418967fa.accept_14_7_1_6_1_3514
  77 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 272 (accept_3_2 76
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 75 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 113 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 272 (accept_3_2 73 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 113 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 272 (Polychromatic418967fa.accept_9_8_5_2_1_422
  71 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 272 (accept_3_2 70
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 113 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 272 (accept_3_2 67 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 113 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 272 (Polychromatic418967fa.accept_7_2_1_6_1_173
  65 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 272 (accept_3_2 64
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 113 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 272 (accept_3_2 61 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 113 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 272
  (Polychromatic418967fa.accept_20_19_13_12_1_2476 59 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 113 272 (accept_3_2 58 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 272 (Polychromatic418967fa.accept_23_10_21_19_1_16679 56
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 272 (accept_3_2 55
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 113 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 272 (accept_3_2 52 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 272 (Polychromatic418967fa.accept_11_6_3_8_1_843
  50 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 272 (accept_3_2 49
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 113 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 272 (accept_3_2 46 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 272 (Polychromatic418967fa.accept_7_2_1_6_1_173
  44 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 272 (accept_3_2 43
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 113 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 41 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 272 (accept_3_2 40 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 272 (Polychromatic418967fa.accept_11_5_3_8_1_454
  38 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 272 (accept_3_2 37
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 272
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 272 (accept_3_2 34 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 272
  (Polychromatic418967fa.accept_21_11_8_20_1_4591 32 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 113 272 (accept_3_2 31 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 113 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 272 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 113
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 272 (accept_3_2 28 113
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 113 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 272 (accept_3_2 25 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 113 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 272 (Polychromatic418967fa.accept_7_2_1_6_1_173
  23 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 272 (accept_3_2 22
  113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 113 272 (Polychromatic418967fa.accept_19_1_18_6_1_3110 20 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 272 (accept_3_2 19 113 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 113 272 (Polychromatic418967fa.accept_25_18_13_22_1_16678 18 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 272 (accept_3_2 16 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 272 (accept_3_2 13 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 272
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 272 (accept_3_2 10 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 272 (accept_3_2 7 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 113 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 272 (accept_3_2 4 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 272 (accept_3_2 1 113 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 272 (allA_of_3_0 112 112 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 272
  (allA_succ_of_accept 110 111 272 (Polychromatic418967fa.accept_13_6_7_12_1_3504 110 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 272 (accept_3_2 109 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 272 (Polychromatic418967fa.accept_13_4_7_12_1_2823 108 111 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 272 (accept_3_2 106 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 104 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 272 (accept_3_2 103 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 102 111
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 272 (accept_3_2 100 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 99 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 272 (accept_3_2 97 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 272 (accept_3_2 94 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 93 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 92 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 272 (accept_3_2 91 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 111
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 272 (accept_3_2 88 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 272 (accept_3_2 85 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 272 (Polychromatic418967fa.accept_13_6_7_12_1_3504 84 111 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 272 (accept_3_2 82 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 272 (accept_3_2 79 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 272 (accept_3_2 76 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 272 (Polychromatic418967fa.accept_13_10_7_12_1_2782 75 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 272 (Polychromatic418967fa.accept_21_11_6_20_1_4589 74 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 272 (accept_3_2 73 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 272 (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 111
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 272 (accept_3_2 70 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 272 (accept_3_2 67 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 272 (accept_3_2 64 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 272 (accept_3_2 61 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 272 (accept_3_2 58 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 272 (Polychromatic418967fa.accept_13_5_7_12_1_2757 57 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 272 (accept_3_2 55 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 111
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 272 (accept_3_2 52 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 272 (accept_3_2 49 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 48 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 272 (accept_3_2 46 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 272 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 272 (accept_3_2 43 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 272 (accept_3_2 40 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 272 (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 272 (accept_3_2 37 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 111
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 272 (accept_3_2 34 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 272 (accept_3_2 31 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 272 (accept_3_2 28 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 272 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 272 (accept_3_2 25 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 272 (accept_3_2 22 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 272 (Polychromatic418967fa.accept_13_8_7_12_1_3637 21 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 272 (Polychromatic418967fa.accept_22_20_1_8_1_13628 20 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 272 (accept_3_2 19 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 111
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 272 (accept_3_2 16 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 272 (accept_3_2 13 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 111 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 272 (accept_3_2 10 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 272 (accept_3_2 7 111 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 272 (accept_3_2 4 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 111 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 272 (Polychromatic418967fa.accept_21_2_6_20_1_6059 2 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 272 (accept_3_2 1 111 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 272 (allA_succ_of_accept 109 110 272 (accept_3_2 109 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 272 2 54 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 107 110 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 272 2 53 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 110 272
  (Polychromatic418967fa.accept_19_10_15_6_1_5772 105 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 110 272 2 52 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 110 272 (accept_3_2 103 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 110 272 2 51 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 110 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 101 110 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 272 2 50 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 110 272 2 49 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 110 272 (accept_3_2 97 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 272 2 48 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 272 2 47 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 272
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 93 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 272 2 46 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 272 (accept_3_2 91 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 272 2 45 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 272 2 44 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 272
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 87 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 272 2 43 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 272 (accept_3_2 85 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 272 2 42 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 110 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 272 2 41 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 272 2 40 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 272 (accept_3_2 79 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 272 2 39 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 272 2 38 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 272
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 75 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 110 272 2 37 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 110 272 (accept_3_2 73 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 272 2 36 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 272 2 35 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 272
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 69 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 110 272 2 34 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 110 272 (accept_3_2 67 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 272 2 33 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 272 2 32 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 272
  (Polychromatic418967fa.accept_15_3_5_2_1_2816 63 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 272 2 31 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 272 (accept_3_2 61 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 272 2 30 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 110 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 272 2 29 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 272 2 28 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 272 (accept_3_2 55 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 272 2 27 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 272 2 26 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 272
  (Polychromatic418967fa.accept_19_13_15_6_1_7131 51 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 110 272 2 25 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 110 272 (accept_3_2 49 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 272 2 24 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 110 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 272 2 23 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 272
  (Polychromatic418967fa.accept_20_5_10_12_1_8200 45 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 110 272 2 22 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 110 272 (accept_3_2 43 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 272 2 21 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 272 2 20 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 272 2 19 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 272 (accept_3_2 37 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 272 2 18 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 110 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 272 2 17 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 272
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 33 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 272 2 16 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 272 (accept_3_2 31 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 272 2 15 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 272 2 14 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 272
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 110 272 2 13 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 110 272 (accept_3_2 25 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 272 2 12 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 110 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 272 2 11 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 272
  (Polychromatic418967fa.accept_19_2_15_6_1_4408 21 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 272 2 10 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 272 (accept_3_2 19 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 272 2 9 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 272 2 8 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 110 272 2 7 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 110 272 (accept_3_2 13 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 272 2 6 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 110 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 272 2 5 55 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 272
  (Polychromatic418967fa.accept_19_9_15_6_1_4396 9 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 272 2 4 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 272 (accept_3_2 7 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  272 2 3 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 110 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 272 2 2 55 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 272 (Polychromatic418967fa.accept_15_3_5_2_1_2816 3 110 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 272 2 1 55 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 272 (accept_3_2 1 110 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 272 (allA_of_3_0 109 109 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 272
  (allA_succ_of_accept 107 108 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 107 108 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 272 2 53 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 272 (Polychromatic418967fa.accept_10_5_8_2_1_517
  105 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 108 272 4 26 27 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 272
  (accept_3_2 103 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 108 272 2 51 54 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 108 272
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 101 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 108 272 4 25 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 108 272 (Polychromatic418967fa.accept_13_8_4_12_1_2753 99 108 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 108 272 2 49 54 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 272 (accept_3_2 97 108 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 108 272 4 24 27 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 108 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 95 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 108 272 2 47 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 108 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 108 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 108 272 4 23 27 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 272 (accept_3_2 91 108 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 108 272 2 45 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 108 272
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 89 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 108 272 4 22 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 108 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 87 108 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 108 272 2 43 54 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 272 (accept_3_2 85 108 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 108 272 4 21 27 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 108 272
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 83 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 108 272 2 41 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 108 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 108 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 108 272 4 20 27 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 272 (accept_3_2 79 108 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 108 272 2 39 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 108 272
  (Polychromatic418967fa.accept_22_11_20_8_1_13603 77 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 108 272 4 19 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 108 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 75 108 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 108 272 2 37 54 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 272 (accept_3_2 73 108 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 108 272 4 18 27 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 108 272
  (Polychromatic418967fa.accept_24_23_12_8_1_16677 71 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 108 272 2 35 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 108 272 (Polychromatic418967fa.accept_19_12_13_6_1_7130 69 108 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 272 4 17 27 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 272 (accept_3_2 67
  108 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 108 272 2 33 54 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 108 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 272 4 16 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 272 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 108 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 272 2 31 54 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 272 (accept_3_2 61 108 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 108 272 4 15 27 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 108 272
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 59 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 272 2 29 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 272 (Polychromatic418967fa.accept_13_5_4_12_1_2058 57 108 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 272 4 14 27 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 272 (accept_3_2 55 108 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 108 272 2 27 54 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 108 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 272 4 13 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 108 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 272 2 25 54 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 272 (accept_3_2 49 108 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 108 272 4 12 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 108 272 (Polychromatic418967fa.accept_13_8_4_12_1_2753
  47 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 272 2 23 54 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 272 4 11 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 272 (accept_3_2 43 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 272 2 21 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 272 (Polychromatic418967fa.accept_13_2_4_12_1_745 41 108 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 272 4 10 27 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 272 2 19 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 272 (accept_3_2 37 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 272 4 9 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 108 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 272 2 17 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 272 (Polychromatic418967fa.accept_13_7_4_12_1_1341
  33 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 272 4 8 27 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 272
  (accept_3_2 31 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 272 2 15 54 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 272
  (Polychromatic418967fa.accept_13_3_4_12_1_36 29 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 272 4 7 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 272 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 108 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 272 2 13 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 272 (accept_3_2 25 108 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 272 4 6 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 108 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 272 2 11 54 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 272
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 272 4 5 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 272 (accept_3_2 19 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  108 272 2 9 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 272 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 108 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 272 4 4 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 272 (Polychromatic418967fa.accept_10_5_8_2_1_517
  15 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 272 2 7 54 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 272
  (accept_3_2 13 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 272 4 3 27 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 272 2 5 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 108 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 272 4 2 27 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 272 (accept_3_2 7 108 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 272 2 3 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 108 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 272 4 1 27 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 272
  (Polychromatic418967fa.accept_13_3_4_12_1_36 3 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 272 2 1 54 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 272 (accept_3_2 1 108 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 272 (allA_succ_of_accept 106 107 272 (accept_3_2 106 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 107 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 107
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 272 (accept_3_2 103 107
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 102 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 101 107 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 272 (accept_3_2 100 107 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 272 (Polychromatic418967fa.accept_12_2_11_8_1_504
  98 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 272 (accept_3_2 97
  107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 96 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 107 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 107 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 272 (accept_3_2 94 107 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 92
  107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 107 272 (accept_3_2 91
  107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 107 272
  (Polychromatic418967fa.accept_19_14_12_6_1_9964 90 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 107 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 89 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 272 (accept_3_2 88 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 272 (accept_3_2 85 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 272 (Polychromatic418967fa.accept_18_11_17_2_1_6349 83 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 272 (accept_3_2 82 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 107 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 272 (accept_3_2 79 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 272 (accept_3_2 76 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 272 (accept_3_2 73 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 272 (Polychromatic418967fa.accept_19_15_12_6_1_8634 72 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 272 (accept_3_2 70 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 272 (accept_3_2 67 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 65 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 272 (accept_3_2 64 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 272 (accept_3_2 61 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 272 (accept_3_2 58 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 272
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 56 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 272 (accept_3_2 55 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 272 (accept_3_2 52 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 272 (accept_3_2 49 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 272 (Polychromatic418967fa.accept_18_11_17_2_1_6349 47 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 272 (accept_3_2 46 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 272
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 272 (accept_3_2 43 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 272 (accept_3_2 40 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 272 (accept_3_2 37 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 272 (accept_3_2 34 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 272 (accept_3_2 31 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 272 (accept_3_2 28 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 272 (accept_3_2 25 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 272 (accept_3_2 22 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 272
  (Polychromatic418967fa.accept_22_20_19_8_1_9003 20 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 107 272 (accept_3_2 19 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 107 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 107 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 107 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 272 (accept_3_2 16 107 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 272 (accept_3_2 13 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 272 (accept_3_2 10 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 272 (accept_3_2 7 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 272 (accept_3_2 4 107 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 272 (accept_3_2 1 107 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 272 (allA_of_3_0 106 106 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 272
  (allA_succ_of_accept 104 105 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 104 105 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 272 (accept_3_2 103 105 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 272 (accept_3_2 100 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 272 (Polychromatic418967fa.accept_13_8_1_12_1_762 99 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 272 (accept_3_2 97 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 272 (Polychromatic418967fa.accept_13_5_1_12_1_740 96 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 272 (accept_3_2 94 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 272 (Polychromatic418967fa.accept_14_8_7_6_1_1159 92 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 272 (accept_3_2 91 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 105
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 272 (accept_3_2 88 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 87 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 272 (accept_3_2 85 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 272 (accept_3_2 82 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 272 (Polychromatic418967fa.accept_22_15_17_8_1_16676 81 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 80 105 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 272 (accept_3_2 79 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 105
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 272 (accept_3_2 76 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 272 (Polychromatic418967fa.accept_25_24_5_22_1_14925 74 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 272 (accept_3_2 73 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 272 (Polychromatic418967fa.accept_19_15_10_6_1_7169 72 105
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 272 (accept_3_2 70 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 272 (accept_3_2 67 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 272 (accept_3_2 64 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 272 (accept_3_2 61 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 272 (Polychromatic418967fa.accept_13_8_1_12_1_762 60 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 272 (accept_3_2 58 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 272 (Polychromatic418967fa.accept_23_10_13_19_1_8547 56 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 272 (accept_3_2 55 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 105
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 272 (accept_3_2 52 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 272 (Polychromatic418967fa.accept_19_13_10_6_1_7147 51 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 272 (accept_3_2 49 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 272 (accept_3_2 46 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 272 (Polychromatic418967fa.accept_25_20_5_22_1_16675 45 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 272 (accept_3_2 43 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 105
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 272 (accept_3_2 40 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 272 (accept_3_2 37 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 105
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 272 (accept_3_2 34 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 272 (accept_3_2 31 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 272 (accept_3_2 28 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 272 (accept_3_2 25 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 272 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 105 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 272 (accept_3_2 22 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 272 (Polychromatic418967fa.accept_19_1_10_6_1_5726 20 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 272 (accept_3_2 19 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 105
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 272 (accept_3_2 16 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 272 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 272 (accept_3_2 13 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 272 (accept_3_2 10 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 272 (Polychromatic418967fa.accept_19_9_10_6_1_4394 9 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 272 (accept_3_2 7 105 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 272 (accept_3_2 4 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 272 (Polychromatic418967fa.accept_13_2_1_12_1_1326 2 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 272 (accept_3_2 1 105 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 272 (allA_succ_of_accept 103 104 272 (accept_3_2 103 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 272 2 51 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 101 104 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 272 4 25 26 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 272
  (Polychromatic418967fa.accept_23_7_12_19_1_16674 99 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 104 272 2 49 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 104 272 (accept_3_2 97 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 272 8 12 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 272 (Polychromatic418967fa.accept_15_5_14_2_1_1876 95 104 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 272 2 47 52 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 93 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 272 4 23 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 272 (accept_3_2 91 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 272 2 45 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 104 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 272 8 11 13 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 272 2 43 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 272 (accept_3_2 85 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 272 4 21 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 272 (Polychromatic418967fa.accept_18_11_14_2_1_5058 83 104 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 272 2 41 52 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 272
  (Polychromatic418967fa.accept_25_6_4_22_1_14853 81 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 104 272 8 10 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 104 272 (accept_3_2 79 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 272 2 39 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 104 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 272 4 19 26 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 272 2 37 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 272 (accept_3_2 73 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 272 8 9 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 104 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 104 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 272 2 35 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 69
  104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 104 272 4 17 26 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 104 272 (accept_3_2 67
  104 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 104 272 2 33 52 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 104 272
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 104 272 8 8 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 104 272 (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 104 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 104 272 2 31 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 104 272 (accept_3_2 61 104 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 104 272 4 15 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 104 272 (Polychromatic418967fa.accept_25_9_4_22_1_13219 59 104
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 272 2 29 52 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 272 8 7 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 104 272 (accept_3_2 55 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  104 272 2 27 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 104 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 104 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 272 4 13 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 51
  104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 104 272 2 25 52 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 104 272 (accept_3_2 49
  104 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 104 272 8 6 13 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 104 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 104 272 2 23 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 104 272 (Polychromatic418967fa.accept_25_20_4_22_1_14855 45 104 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 104 272 4 11 26 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 104 272 (accept_3_2 43 104 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 104 272 2 21 52 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 104 272
  (Polychromatic418967fa.accept_19_3_9_6_1_12696 41 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 104 272 8 5 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 104 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 104 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 104 272 2 19 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 104 272 (accept_3_2 37 104 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 104 272 4 9 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 104 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 272 2 17 52 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 272 8 4 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 104 272 (accept_3_2 31 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  104 272 2 15 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 104 272 (Polychromatic418967fa.accept_18_11_14_2_1_5058 29 104 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 272 4 7 26 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 272 2 13 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 272 (accept_3_2 25 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 272 8 3 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 104 272 (Polychromatic418967fa.accept_29_23_17_11_1_16673 23 104 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 272 2 11 52 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 272 4 5 26 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 272 (accept_3_2 19 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 272 2 9 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 104 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 272 8 2 13 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 272 2 7 52 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 272 (accept_3_2 13
  104 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 272 4 3 26 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 272
  (Polychromatic418967fa.accept_18_11_14_2_1_5058 11 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 104 272 2 5 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 104 272 (Polychromatic418967fa.accept_22_9_16_8_1_4058 9 104 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 272 8 1 13 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 272 (accept_3_2 7 104 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 272 2 3 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 272 (Polychromatic418967fa.accept_15_5_14_2_1_1876
  5 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 272 4 1 26 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 272 2 1 52 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 272 (accept_3_2 1 104 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 272 (allA_of_3_0 103 103 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 272 (allA_succ_of_accept 101
  102 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 101 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 272 2 50 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 102 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 272 2 49 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 272 (accept_3_2 97 102 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 272 2 48 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 272 2 47 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 102 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 272 2 46 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 272 (accept_3_2 91 102 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 272 2 45 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 89
  102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 272 2 44 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 102 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 102 272 2 43 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 102 272 17 5 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 102 272 2 42 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 102 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 83 102 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 272 2 41 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 102 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 102 272 2 40 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 102 272 (accept_3_2 79 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 272 2 39 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 102 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 272 2 38 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 272 2 37 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 272 (accept_3_2 73 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 272 2 36 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 102 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 272 2 35 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 272 34 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 102 272 (accept_3_2 67 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66
  102 272 2 33 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 102 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 102 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 272 2 32 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 272 (Polychromatic418967fa.accept_12_3_6_8_1_969
  63 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 272 2 31 51 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 272
  (accept_3_2 61 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 102 272 2 30 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 102 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 272 2 29 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 57 102 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 272 2 28 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 272 (accept_3_2 55 102 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 102 272 2 27 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 102 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 53
  102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 272 2 26 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 272 17 3 6 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 272 2 25 51 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 272
  (accept_3_2 49 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 102 272 2 24 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 102 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 272 2 23 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 102 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 272 2 22 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 272 (accept_3_2 43 102 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 102 272 2 21 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 102 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 41
  102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 272 2 20 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 272
  (Polychromatic418967fa.accept_11_6_3_8_1_843 39 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 272 2 19 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 272 (accept_3_2 37 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 272 2 18 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 102 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 272 34 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 33
  102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 272 2 16 51 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 272 (accept_3_2 31
  102 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 102 272 2 15 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 102 272
  (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 102 272 2 14 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 102 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 102 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 272 2 13 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 272 (accept_3_2 25 102 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 272 2 12 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 272 2 11 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 102 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 272 2 10 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 272 (accept_3_2 19 102 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 102 272 2 9 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 102 272 17 1 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 16 102 272 2 8 51 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 272 2 7 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 272 (accept_3_2 13 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 272 2 6 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 272 (Polychromatic418967fa.accept_21_11_18_20_1_1877 11 102 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 272 2 5 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 272 2 4 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 272 (accept_3_2 7 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  272 2 3 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 102 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 272 2 2 51 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 102 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 272 2 1 51 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 272 (accept_3_2 1 102 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 272 (allA_succ_of_accept 100 101 272 (accept_3_2 100 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 98 101
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 272 (accept_3_2 97 101
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 272
  (Polychromatic418967fa.accept_10_6_1_2_1_874 96 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 95 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 272 (accept_3_2 94 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 272
  (Polychromatic418967fa.accept_21_8_17_20_1_3142 92 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 101 272 (accept_3_2 91 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 101 272 (Polychromatic418967fa.accept_22_2_13_8_1_13622 90 101 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 272 (Polychromatic418967fa.accept_10_9_1_2_1_522
  89 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 272 (accept_3_2 88
  101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 87 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 101 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 272 (accept_3_2 85 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 101 272 (Polychromatic418967fa.accept_13_6_10_12_1_2049 84 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 272
  (Polychromatic418967fa.accept_10_3_1_2_1_521 83 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 272 (accept_3_2 82 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 80 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 272 (accept_3_2 79 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 272 (Polychromatic418967fa.accept_24_6_5_8_1_16652 78 101
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 272
  (Polychromatic418967fa.accept_21_14_17_20_1_12259 77 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 101 272 (accept_3_2 76 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 74 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 272 (accept_3_2 73 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 72
  101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 272
  (Polychromatic418967fa.accept_11_5_2_8_1_866 71 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 272 (accept_3_2 70 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 272 (Polychromatic418967fa.accept_18_14_11_2_1_5068 68 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 272 (accept_3_2 67 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 101
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 272 (accept_3_2 64 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 272 (accept_3_2 61 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 272
  (Polychromatic418967fa.accept_10_9_1_2_1_522 59 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 272 (accept_3_2 58 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 272 (accept_3_2 55 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 54 101
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 272 (accept_3_2 52 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 272 (accept_3_2 49 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 272 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 101
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 272
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 47 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 101 272 (accept_3_2 46 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 272 (accept_3_2 43 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 272
  (Polychromatic418967fa.accept_31_11_8_24_1_16672 42 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 41 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 272 (accept_3_2 40 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 272
  (Polychromatic418967fa.accept_11_5_2_8_1_866 38 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 272 (accept_3_2 37 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 272 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 272 (accept_3_2 34 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 272 (accept_3_2 31 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 272 (accept_3_2 28 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 272
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 272 (accept_3_2 25 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 272 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 272 (accept_3_2 22 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 272
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 101 272 (accept_3_2 19 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 101 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 272 (Polychromatic418967fa.accept_18_17_11_2_1_7782 17 101
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 272 (accept_3_2 16 101
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 101 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 272 (accept_3_2 13 101 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 101 272 (Polychromatic418967fa.accept_24_12_5_8_1_13359 12 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 272 (accept_3_2 10 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 272 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 272 (accept_3_2 7 101 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 101 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 272
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 272 (accept_3_2 4 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 101 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 272 (accept_3_2 1 101 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 272 (allA_of_3_0 100 100 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 272 (allA_succ_of_accept 98 99
  272 (Polychromatic418967fa.accept_13_7_8_12_1_2810 98 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 272 (accept_3_2 97 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 99 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 272 (accept_3_2 94 99 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 93
  99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 272
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 92 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 272 (accept_3_2 91 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 272 (accept_3_2 88 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 87 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 272 (accept_3_2 85 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 272 (Polychromatic418967fa.accept_27_3_18_2_1_16671 84 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 272 (accept_3_2 82 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 81 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 272
  (Polychromatic418967fa.accept_22_14_11_8_1_7212 80 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 272 (accept_3_2 79 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 272 (accept_3_2 76 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 272
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 74 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 272 (accept_3_2 73 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 272 (accept_3_2 70 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 272 (Polychromatic418967fa.accept_13_4_8_12_1_3526 69 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 272 (accept_3_2 67 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 272 (accept_3_2 64 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 272 (Polychromatic418967fa.accept_14_7_1_6_1_3514 63 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 272
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 62 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 272 (accept_3_2 61 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 272 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 272 (accept_3_2 58 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 272
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 56 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 272 (accept_3_2 55 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 272 (accept_3_2 52 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 272
  (Polychromatic418967fa.accept_19_12_4_6_1_7163 50 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 272 (accept_3_2 49 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 272 (Polychromatic418967fa.accept_13_9_8_12_1_2031 48 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 272 (accept_3_2 46 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 272 (Polychromatic418967fa.accept_22_1_11_8_1_16670 45 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 272 (accept_3_2 43 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 272 (accept_3_2 40 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 39 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 272
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 272 (accept_3_2 37 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 272 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 272 (accept_3_2 34 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 272
  (Polychromatic418967fa.accept_19_13_4_6_1_9960 32 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 272 (accept_3_2 31 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 272 (accept_3_2 28 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 272 (accept_3_2 25 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 272 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 272 (accept_3_2 22 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 272
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 20 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 272 (accept_3_2 19 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 272 (accept_3_2 16 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 272 (Polychromatic418967fa.accept_19_15_4_6_1_8666 15 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 272
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 272 (accept_3_2 13 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 272 (accept_3_2 10 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 99 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 272
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 272 (accept_3_2 7 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 272 (accept_3_2 4 99 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 3 99 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  99 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 272 (accept_3_2 1 99 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  272 (allA_succ_of_accept 97 98 272 (accept_3_2 97 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 272 2 48 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 98 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 272 2 47 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 93
  98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 272 2 46 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 272 (accept_3_2 91
  98 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 272 2 45 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 272
  (Polychromatic418967fa.accept_12_5_2_8_1_172 89 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 272 2 44 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 87 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 272 2 43 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 272 (accept_3_2 85 98 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 272 2 42 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 272 (Polychromatic418967fa.accept_12_11_2_8_1_511
  83 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 272 2 41 49 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 272
  (Polychromatic418967fa.accept_15_6_8_2_1_104 81 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 272 2 40 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 272 (accept_3_2 79 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 272 2 39 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 272 2 38 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 272 2 37 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 272 (accept_3_2 73 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 272 2 36 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 272 2 35 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 272 2 34 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 272 (accept_3_2 67 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 272 2 33 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 272 2 32 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 272
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 272 2 31 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 272 (accept_3_2 61 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 272 2 30 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 272 2 29 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 272 2 28 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 272 (accept_3_2 55 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 272 2 27 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 53 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 272 2 26 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 272 2 25 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 272 (accept_3_2 49 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 272 2 24 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 272 2 23 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 272 2 22 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 272 (accept_3_2 43 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 272 2 21 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 272 2 20 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 272 2 19 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 272 (accept_3_2 37 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 272 2 18 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 272 2 17 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 272 2 16 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 272 (accept_3_2 31 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 272 2 15 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 272 2 14 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 272
  (Polychromatic418967fa.accept_19_8_3_6_1_9982 27 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 272 2 13 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 272 (accept_3_2 25 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 272 2 12 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 272 2 11 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 272 2 10 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 98 272 (accept_3_2 19 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 272 2 9 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 272 2 8 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 272 2 7 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 272 (accept_3_2 13
  98 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 272 2 6 49 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 272
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 98 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 272 2 5 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 98 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 272 2 4 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 272 (accept_3_2 7 98 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 272 2 3 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 272 2 2 49 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 98
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 272 2 1 49 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 272 (accept_3_2 1 98
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  272 (allA_of_3_0 97 97 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 272 (allA_succ_of_accept 95 96 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 95 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 272 2 47 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 96 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 272 4 23 24 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 272 (accept_3_2 91 96 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 272 2 45 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 89
  96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 272 8 11 12 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 272
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 87 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 272 2 43 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 272 (accept_3_2 85 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 272 4 21 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 272 (Polychromatic418967fa.accept_14_13_12_6_1_2735 83 96 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 272 2 41 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 81
  96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 272 16 5 6 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 272 (accept_3_2 79
  96 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 272 2 39 48 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 272 4 19 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 96 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 96 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 272 2 37 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 272 (accept_3_2 73 96 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 272 8 9 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 96 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 96 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 272 2 35 48 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 272
  (Polychromatic418967fa.accept_13_4_5_12_1_751 69 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 272 4 17 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 272 (accept_3_2 67 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96
  272 2 33 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 96 272 (Polychromatic418967fa.accept_25_15_21_22_1_14878 65 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 96 272 16 4 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 96 272 (Polychromatic418967fa.accept_18_9_6_2_1_2619 63 96 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 272 2 31 48 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 272 (accept_3_2 61 96 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 272 4 15 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 59
  96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 272 2 29 48 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 272 8 7 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 96 272 (accept_3_2 55 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96
  272 2 27 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 96 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 96 272 4 13 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 96 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 96 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 272 2 25 48 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 272 (accept_3_2 49 96 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 272 16 3 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 272 (Polychromatic418967fa.accept_13_8_5_12_1_2755
  47 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 272 2 23 48 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 272
  (Polychromatic418967fa.accept_13_6_5_12_1_307 45 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 272 4 11 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 272 (accept_3_2 43 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96
  272 2 21 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 96 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 96 272 8 5 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 96 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 272 2 19 48 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 272 (accept_3_2 37 96 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 272 4 9 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 272 2 17 48 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 272
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 272 16 2 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 272 (accept_3_2 31 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  272 2 15 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 96 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 272 4 7 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 272 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 96 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 272 2 13 48 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 272 (accept_3_2 25 96 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 272 8 3 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 272 2 11 48 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 272 4 5 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 272 (accept_3_2 19 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  272 2 9 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 272 16 1 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 272 2 7 48 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 272 (accept_3_2 13 96 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 272 4 3 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 272 2 5 48 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 272
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 272 8 1 12 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 272 (accept_3_2 7 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 272
  2 3 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 272 4 1 24 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 272 2 1 48 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 272 (accept_3_2 1 96 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 272
  (allA_succ_of_accept 94 95 272 (accept_3_2 94 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 272 (Polychromatic418967fa.accept_11_4_7_8_1_1926 92 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 272 (accept_3_2 91 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 272 (Polychromatic418967fa.accept_20_10_15_12_1_11131 90 95 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 89 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 272 (accept_3_2 88 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 86 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 272 (accept_3_2 85 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 272
  (Polychromatic418967fa.accept_10_3_5_2_1_38 83 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 272 (accept_3_2 82 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 272 (accept_3_2 79 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 272
  (Polychromatic418967fa.accept_10_7_5_2_1_880 77 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 272 (accept_3_2 76 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 272 (accept_3_2 73 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 272 (accept_3_2 70 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 272 (accept_3_2 67 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 272 (accept_3_2 64 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 272 (accept_3_2 61 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 272 (accept_3_2 58 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 272 (accept_3_2 55 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 272 (accept_3_2 52 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 272 (accept_3_2 49 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 272 (accept_3_2 46 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 272 (accept_3_2 43 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 272
  (Polychromatic418967fa.accept_13_2_4_12_1_745 41 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 272 (accept_3_2 40 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 272 (accept_3_2 37 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 272 (Polychromatic418967fa.accept_24_12_23_8_1_13335 36 95 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 272 (accept_3_2 34 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 272 (Polychromatic418967fa.accept_22_10_7_8_1_16669 32 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 272 (accept_3_2 31 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 95 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 272
  (Polychromatic418967fa.accept_13_3_4_12_1_36 29 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 272 (accept_3_2 28 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 272 (accept_3_2 25 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 272 (accept_3_2 22 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 272 (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 272 (accept_3_2 19 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 95 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 272 (accept_3_2 16 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 272 (accept_3_2 13 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 272
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 272 (accept_3_2 10 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 272 (accept_3_2 7 95 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 95 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 272 (accept_3_2 4 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 95 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 272 (accept_3_2 1 95 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 272
  (allA_of_3_0 94 94 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 272 (allA_succ_of_accept 92 93 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 92 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 272 (accept_3_2 91 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 90 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 272 (accept_3_2 88 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 86 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 272 (accept_3_2 85 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 272 (Polychromatic418967fa.accept_13_6_2_12_1_2802 84 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 272 (accept_3_2 82 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 272 (accept_3_2 79 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 272 (accept_3_2 76 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 75 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 272 (accept_3_2 73 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 272 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 272 (accept_3_2 70 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 272 (accept_3_2 67 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 272 (accept_3_2 64 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 272 (Polychromatic418967fa.accept_18_9_3_2_1_3814 63 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 272 (accept_3_2 61 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 272 (accept_3_2 58 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 272
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 56 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 272 (accept_3_2 55 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 272 (accept_3_2 52 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 272 (accept_3_2 49 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 272 (accept_3_2 46 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 272 (accept_3_2 43 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 272 (accept_3_2 40 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 272 (accept_3_2 37 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 272 (accept_3_2 34 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 272 (accept_3_2 31 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 272 (accept_3_2 28 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 272 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 272 (accept_3_2 25 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 272 (accept_3_2 22 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 272
  (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 272 (accept_3_2 19 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 272 (accept_3_2 16 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 272 (accept_3_2 13 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 272 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 272 (accept_3_2 10 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 272 (Polychromatic418967fa.accept_18_9_3_2_1_3814 9 93 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 272 (accept_3_2 7 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 272 (accept_3_2 4 93 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 2
  93 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 272 (accept_3_2 1 93 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 272
  (allA_succ_of_accept 91 92 272 (accept_3_2 91 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  272 2 45 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 272 4 22 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 272 (Polychromatic418967fa.accept_19_11_16_6_1_7155 87 92 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 272 2 43 46 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 272 (accept_3_2 85 92 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 272 4 21 23 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 272
  (Polychromatic418967fa.accept_13_5_1_12_1_740 83 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 272 2 41 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 272 (Polychromatic418967fa.accept_22_15_4_8_1_10600 81 92 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 272 4 20 23 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 272 (accept_3_2 79 92 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 272 2 39 46 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 272
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 77 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 92 272 4 19 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 92 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 92 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 92 272 2 37 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 92 272 (accept_3_2 73 92 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 72 92 272 4 18 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 92 272 (Polychromatic418967fa.accept_25_21_17_22_1_16668 71 92
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 272 2 35 46 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 272
  (Polychromatic418967fa.accept_19_12_16_6_1_7175 69 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 92 272 4 17 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 92 272 (accept_3_2 67 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92
  272 2 33 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  65 92 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 92 272 4 16 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 92 272 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 92 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 272 2 31 46 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 272 (accept_3_2 61 92 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 272 4 15 23 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 272
  (Polychromatic418967fa.accept_21_17_8_20_1_7805 59 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 92 272 2 29 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 92 272 (Polychromatic418967fa.accept_13_5_1_12_1_740 57 92 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 92 272 4 14 23 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 92 272 (accept_3_2 55 92 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92 272 2 27 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 92 272 (Polychromatic418967fa.accept_19_15_16_6_1_9955
  53 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 272 4 13 23 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 92 272 2 25 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 92 272 (accept_3_2 49 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 92 272 4 12 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 92 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 92 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 92 272 2 23 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 92 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  45 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 272 4 11 23 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 272 (accept_3_2 43
  92 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 272 2 21 46 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 272
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 41 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 92 272 4 10 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 92 272 (Polychromatic418967fa.accept_24_15_20_8_1_13325 39 92 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 272 2 19 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 272 (accept_3_2 37 92 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 272 4 9 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 92 272 (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 92 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 272 2 17 46 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 272 4 8 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 92 272 (accept_3_2 31 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92
  272 2 15 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 92 272 (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 92 272 4 7 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 92 272 (Polychromatic418967fa.accept_19_8_16_6_1_5804 27 92 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 272 2 13 46 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 272 (accept_3_2 25 92 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 272 4 6 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 92 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 272 2 11 46 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 272
  (Polychromatic418967fa.accept_13_8_1_12_1_762 21 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 272 4 5 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 272 (accept_3_2 19 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  272 2 9 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 272 (Polychromatic418967fa.accept_21_17_8_20_1_7805 17 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 272 4 4 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 272 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 92 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 272 2 7 46 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 272 (accept_3_2 13 92 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 272 4 3 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 272 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 92 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 272 2 5 46 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 272 4 2 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 272 (accept_3_2 7 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 272
  2 3 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 272 4 1 23 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 272 (Polychromatic418967fa.accept_19_3_16_6_1_1987 3 92 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 272 2 1 46 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 272 (accept_3_2 1 92 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 272
  (allA_of_3_0 91 91 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 272 (allA_succ_of_accept 89 90 272
  (Polychromatic418967fa.accept_21_5_6_20_1_16667 89 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 272 2 44 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 90 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 87 90 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 272 2 43 45 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 272 (accept_3_2 85 90 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 272 2 42 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 272 (Polychromatic418967fa.accept_19_7_14_6_1_9987
  83 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 272 2 41 45 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 272 2 40 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 272 (accept_3_2 79 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 272 2 39 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 272 (Polychromatic418967fa.accept_19_1_14_6_1_1983 77 90 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 272 2 38 45 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 272 2 37 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 90 272 (accept_3_2 73 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 272 2 36 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 71 90 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 272 2 35 45 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 272 2 34 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 90 272 (accept_3_2 67 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 272 2 33 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 272 (Polychromatic418967fa.accept_19_8_14_6_1_5802 65 90 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 272 2 32 45 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 272 2 31 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 272 (accept_3_2 61 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 272 2 30 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 272 (Polychromatic418967fa.accept_22_15_2_8_1_13605 59 90 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 272 2 29 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 272 2 28 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 90 272 (accept_3_2 55 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 272 2 27 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 272 (Polychromatic418967fa.accept_20_13_10_12_1_2462 53 90 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 272 2 26 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 272 2 25 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 90 272 (accept_3_2 49 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 272 2 24 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 272 (Polychromatic418967fa.accept_19_9_14_6_1_2014 47 90 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 272 2 23 45 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 272 2 22 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 90 272 (accept_3_2 43 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 272 2 21 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 272 (Polychromatic418967fa.accept_25_16_15_22_1_16666 41 90 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 272 2 20 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 272 2 19 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 90 272 (accept_3_2 37 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 272 2 18 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 272 (Polychromatic418967fa.accept_20_15_10_12_1_13874 35 90 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 272 2 17 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 272 2 16 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 272 (accept_3_2 31 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 272 2 15 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 272 (Polychromatic418967fa.accept_19_10_14_6_1_5819 29 90 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 272 2 14 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 272
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 272 2 13 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 90 272 (accept_3_2 25 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 272 2 12 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 272 (Polychromatic418967fa.accept_20_3_10_12_1_11106 23 90 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 272 2 11 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 272 2 10 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 90 272 (accept_3_2 19 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 272 2 9 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 272 (Polychromatic418967fa.accept_23_17_21_19_1_16665 17 90 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 272 2 8 45 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 90 272 2 7 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 272 (accept_3_2 13 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90
  272 2 6 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  90 272 (Polychromatic418967fa.accept_19_11_14_6_1_4378 11 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 272 2 5 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 90 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 90 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 272 2 4 45 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 272 (accept_3_2 7 90 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 272 2 3 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 90 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 272 2 2 45 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 272 2 1 45 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 272 (accept_3_2 1 90 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 272
  (allA_succ_of_accept 88 89 272 (accept_3_2 88 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 272 (accept_3_2 85 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 272
  (Polychromatic418967fa.accept_14_13_5_6_1_2747 83 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 272 (accept_3_2 82 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 272 (Polychromatic418967fa.accept_15_5_14_2_1_1876 80 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 272 (accept_3_2 79 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 89 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 272 (accept_3_2 76 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 272 (accept_3_2 73 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 272 (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 272 (accept_3_2 70 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 272 (accept_3_2 67 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 272
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 272 (accept_3_2 64 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 272 (accept_3_2 61 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 272 (accept_3_2 58 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 272 (Polychromatic418967fa.accept_13_4_11_12_1_1318 56 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 272 (accept_3_2 55 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 272 (Polychromatic418967fa.accept_23_8_20_19_1_10271 54 89
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 272 (accept_3_2 52 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 272 (accept_3_2 49 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 272
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 272 (accept_3_2 46 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 272 (Polychromatic418967fa.accept_18_8_17_2_1_1557 44 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 272 (accept_3_2 43 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 272 (accept_3_2 40 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 272 (accept_3_2 37 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 272
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 272 (accept_3_2 34 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 272 (accept_3_2 31 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 272 (accept_3_2 28 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 272 (accept_3_2 25 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 272 (accept_3_2 22 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 272 (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 272 (accept_3_2 19 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 89 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 272
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 272 (accept_3_2 16 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 272 (accept_3_2 13 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 272 (accept_3_2 10 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 272 (accept_3_2 7 89 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 89 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 272 (accept_3_2 4 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 89 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 272 (accept_3_2 1 89 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 272 (allA_of_3_0 88 88 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 272
  (allA_succ_of_accept 86 87 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 272 (accept_3_2 85 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 272 (accept_3_2 82 87
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 272 (accept_3_2 79 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 272 (accept_3_2 76 87
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 74 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 272 (accept_3_2 73 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 272 (accept_3_2 70 87
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 272
  (Polychromatic418967fa.accept_10_9_7_2_1_887 69 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 272 (accept_3_2 67 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 272 (accept_3_2 64 87
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 272
  (Polychromatic418967fa.accept_15_3_12_2_1_507 63 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 272 (accept_3_2 61 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 272 (accept_3_2 58 87
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 272 (Polychromatic418967fa.accept_19_18_11_6_1_5768 56 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 272 (accept_3_2 55 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 272 (accept_3_2 52 87
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 272 (Polychromatic418967fa.accept_7_2_3_6_1_4
  51 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 272 (accept_3_2 49 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 272 (accept_3_2 46 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 87 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 272 (accept_3_2 43 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 272 (accept_3_2 40 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 272
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 272 (accept_3_2 37 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 272 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 272 (accept_3_2 34 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 87 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 272 (accept_3_2 31 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 272 (accept_3_2 28 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 272 (Polychromatic418967fa.accept_21_6_3_20_1_6053 27 87 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 272 (accept_3_2 25 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 272 (accept_3_2 22 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 272
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 272 (accept_3_2 19 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 272 (accept_3_2 16 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 87 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 272 (accept_3_2 13 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 272 (accept_3_2 10 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 272 (accept_3_2 7 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 87 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 272 (accept_3_2 4 87 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 272 (accept_3_2 1 87 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 272
  (allA_succ_of_accept 85 86 272 (accept_3_2 85 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  272 2 42 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 272 2 41 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 86 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 272 2 40 43 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 272 (accept_3_2 79 86 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 272 2 39 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 272
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 272 2 38 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 272 2 37 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 272 (accept_3_2 73 86 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 272 2 36 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 71
  86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 272 2 35 43 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 272 2 34 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 272 (accept_3_2 67 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 272 2 33 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 65 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 272 2 32 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 272
  (Polychromatic418967fa.accept_22_19_20_8_1_8920 63 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 272 2 31 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 272 (accept_3_2 61 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 272 2 30 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 272 2 29 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 272 2 28 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 272 (accept_3_2 55 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 272 2 27 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 272 2 26 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 272 2 25 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 272 (accept_3_2 49 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 272 2 24 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 272 2 23 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 272 2 22 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 272 (accept_3_2 43 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 272 2 21 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 272 2 20 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 272 2 19 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 272 (accept_3_2 37 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 272 2 18 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 272 2 17 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 272 2 16 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 272 (accept_3_2 31 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 272 2 15 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 272 2 14 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 272
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 272 2 13 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 272 (accept_3_2 25 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 272 2 12 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 272 2 11 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 272 2 10 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 272 (accept_3_2 19 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 272 2 9 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 86 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 272 2 8 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 272 2 7 43 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 272 (accept_3_2 13
  86 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 272 2 6 43 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 86 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 272 2 5 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 272 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 86 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 272 2 4 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 272 (accept_3_2 7 86 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 272 2 3 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 86 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 272 2 2 43 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 272 2 1 43 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 272 (accept_3_2 1 86
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 272
  (allA_of_3_0 85 85 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 272 (allA_succ_of_accept 83 84 272
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 83 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 272 2 41 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 272 (Polychromatic418967fa.accept_11_4_7_8_1_1926 81 84 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 272 4 20 21 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 272 (accept_3_2 79 84 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 272 2 39 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 77
  84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 272 4 19 21 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 272
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 75 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 272 2 37 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 272 (accept_3_2 73 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 272 4 18 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 272 2 35 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69
  84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 272 4 17 21 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 272 (accept_3_2 67
  84 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 272 2 33 42 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 272
  (Polychromatic418967fa.accept_24_17_12_8_1_2990 65 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 272 4 16 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 272 (Polychromatic418967fa.accept_22_19_18_8_1_8915 63 84 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 272 2 31 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 272 (accept_3_2 61 84 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 272 4 15 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 272 2 29 42 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 272 4 14 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 272 (accept_3_2 55 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  272 2 27 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 84 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 272 4 13 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 272 2 25 42 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 272 (accept_3_2 49 84 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 272 4 12 21 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 47 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 272 2 23 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 84 272 (Polychromatic418967fa.accept_19_7_8_6_1_3123 45 84 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 272 4 11 21 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 272 (accept_3_2 43 84 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 272 2 21 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 41
  84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 272 4 10 21 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 272
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 272 2 19 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 84 272 (accept_3_2 37 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 272 4 9 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 272 2 17 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33
  84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 272 4 8 21 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 272 (accept_3_2 31
  84 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 272 2 15 42 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 272
  (Polychromatic418967fa.accept_22_7_18_8_1_13589 29 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 272 4 7 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 84 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 272 2 13 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 272 (accept_3_2 25 84 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 272 4 6 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 84 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 272 2 11 42 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 272
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 21 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 272 4 5 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 272 (accept_3_2 19 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  272 2 9 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 272 4 4 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 272 2 7 42 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 272 (accept_3_2 13 84 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 272 4 3 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 272 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 84 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 272 2 5 42 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 272
  (Polychromatic418967fa.accept_22_9_18_8_1_8979 9 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 272 4 2 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 272 (accept_3_2 7 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 272
  2 3 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 272 4 1 21 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 272 (Polychromatic418967fa.accept_18_3_12_2_1_2639 3 84 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 272 2 1 42 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 272 (accept_3_2 1 84 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 83 272 (allA_succ_of_accept 82 83 272 (accept_3_2 82 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 83 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 80 83 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 272 (accept_3_2 79 83 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 272 (Polychromatic418967fa.accept_25_3_8_22_1_9734
  78 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 272
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 77 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 272 (accept_3_2 76 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 272 (accept_3_2 73 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 272 (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 272
  (Polychromatic418967fa.accept_10_1_3_2_1_220 71 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 272 (accept_3_2 70 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 68 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 272 (accept_3_2 67 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 272 (Polychromatic418967fa.accept_13_1_5_12_1_306 66 83 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 272
  (Polychromatic418967fa.accept_10_5_3_2_1_899 65 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 272 (accept_3_2 64 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 272 (accept_3_2 61 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 272 (Polychromatic418967fa.accept_13_8_5_12_1_2755 60 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 272
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 59 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 272 (accept_3_2 58 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 272 (Polychromatic418967fa.accept_13_4_5_12_1_751 56 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 272 (accept_3_2 55 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 272 (Polychromatic418967fa.accept_13_2_5_12_1_2043 54 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 272
  (Polychromatic418967fa.accept_13_1_5_12_1_306 53 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 272 (accept_3_2 52 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 272 (accept_3_2 49 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 272 (Polychromatic418967fa.accept_25_23_8_22_1_14830 48 83 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 272
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 272 (accept_3_2 46 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 272 (Polychromatic418967fa.accept_23_21_14_19_1_16664 44 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 272 (accept_3_2 43 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 272 (Polychromatic418967fa.accept_24_18_11_8_1_11715 42 83
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 272
  (Polychromatic418967fa.accept_10_1_3_2_1_220 41 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 272 (accept_3_2 40 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 272 (accept_3_2 37 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 272
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 272 (accept_3_2 34 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 272 (Polychromatic418967fa.accept_13_6_5_12_1_307 32 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 272 (accept_3_2 31 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 272 (Polychromatic418967fa.accept_13_4_5_12_1_751 30 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 272
  (Polychromatic418967fa.accept_20_9_3_12_1_6627 29 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 272 (accept_3_2 28 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 272 (accept_3_2 25 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 272 (Polychromatic418967fa.accept_15_9_8_2_1_1109 24 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 272
  (Polychromatic418967fa.accept_25_23_8_22_1_14830 23 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 83 272 (accept_3_2 22 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 272 (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 83
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 272 (accept_3_2 19 83 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 272 (Polychromatic418967fa.accept_19_18_7_6_1_4367
  18 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 272
  (Polychromatic418967fa.accept_13_4_5_12_1_751 17 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 272 (accept_3_2 16 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 272 (accept_3_2 13 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 272
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 272 (accept_3_2 10 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 272 (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 272 (accept_3_2 7 83 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 272 (Polychromatic418967fa.accept_13_6_5_12_1_307 6 83 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 272
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 272 (accept_3_2 4 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 83 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 272 (accept_3_2 1 83 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 272 (allA_of_3_0 82 82 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 272
  (allA_succ_of_accept 80 81 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 272 (accept_3_2 79 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 78 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 272 (accept_3_2 76 81
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 272 (Polychromatic418967fa.accept_13_9_3_12_1_2025 74 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 272 (accept_3_2 73 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 272 (accept_3_2 70 81
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 272
  (Polychromatic418967fa.accept_10_9_1_2_1_522 69 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 272 (accept_3_2 67 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 272 (accept_3_2 64 81
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 272
  (Polychromatic418967fa.accept_10_3_1_2_1_521 63 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 272 (Polychromatic418967fa.accept_11_7_4_8_1_1371 62 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 272 (accept_3_2 61 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 272 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59
  81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 272 (accept_3_2 58 81
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 272
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 57 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 272 (accept_3_2 55 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 272 (accept_3_2 52 81
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 272 (Polychromatic418967fa.accept_22_6_15_8_1_16663 50 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 272 (accept_3_2 49 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 272 (Polychromatic418967fa.accept_13_9_3_12_1_2025 48 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 272 (accept_3_2 46 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 272 (accept_3_2 43 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 272 (accept_3_2 40 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 272 (accept_3_2 37 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 272 (accept_3_2 34 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 272 (Polychromatic418967fa.accept_21_11_18_20_1_1877 32 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 272 (accept_3_2 31 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 272 (accept_3_2 28 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 272 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 272 (accept_3_2 25 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 272 (accept_3_2 22 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 21 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 272 (Polychromatic418967fa.accept_19_1_5_6_1_5811 20 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 272 (accept_3_2 19 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 272 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 272 (accept_3_2 16 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 272 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 272 (Polychromatic418967fa.accept_19_14_5_6_1_12685 14 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 272 (accept_3_2 13 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 272 (accept_3_2 10 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 272 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 272 (accept_3_2 7 81 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 81 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 272 (accept_3_2 4 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 272 (accept_3_2 1 81 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 272 (allA_succ_of_accept 79 80 272 (accept_3_2 79 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 80 272 2 39 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 80 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 80 272 4 19 20 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 80 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 80 272 2 37 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 80 272 (accept_3_2 73 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 80 272 8 9 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 80 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 71 80 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 272 2 35 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 69
  80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 272 4 17 20 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 272 (accept_3_2 67
  80 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 272 2 33 40 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 80 272 16 4 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 80 272 (Polychromatic418967fa.accept_15_3_5_2_1_2816 63 80 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 272 2 31 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 272 (accept_3_2 61 80 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 272 4 15 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 272 2 29 40 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 272 8 7 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 272 (accept_3_2 55 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  272 2 27 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 80 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 272 4 13 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 80 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 272 2 25 40 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 272 (accept_3_2 49 80 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 272 16 3 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 272
  (Polychromatic418967fa.accept_27_20_26_2_1_16657 47 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 80 272 2 23 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 80 272 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 80 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 80 272 4 11 20 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 272 (accept_3_2 43 80 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 272 2 21 40 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 272 8 5 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 80 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 272 2 19 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 272 (accept_3_2 37 80 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 272 4 9 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 80 272 (Polychromatic418967fa.accept_18_17_8_2_1_2622 35 80 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 272 2 17 40 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 272 16 2 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 272 (accept_3_2 31 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  272 2 15 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 80 272 (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 272 4 7 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 80 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 272 2 13 40 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 272 (accept_3_2 25 80 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 272 8 3 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 272 2 11 40 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 272 4 5 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 272 (accept_3_2 19 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  272 2 9 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 272 16 1 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 80 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 272 2 7 40 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 272 (accept_3_2 13 80 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 272 4 3 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 272 2 5 40 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 272 8 1 10 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 272 (accept_3_2 7 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 272
  2 3 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 272 4 1 20 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 80 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 272 2 1 40 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 272 (accept_3_2 1 80 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 272 (allA_of_3_0 79 79 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 272
  (allA_succ_of_accept 77 78 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 78 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 272 2 38 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 75
  78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 272 2 37 39 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 272 (accept_3_2 73
  78 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 272 2 36 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 272 2 35 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 78 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 69 78 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 272 2 34 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 272 (accept_3_2 67 78 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 272 2 33 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 65
  78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 272 2 32 39 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 272 2 31 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 272 (accept_3_2 61 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 272 2 30 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 78 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 272 2 29 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 272 2 28 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 272 (accept_3_2 55 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 272 2 27 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 78 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 272 2 26 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 272 2 25 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 272 (accept_3_2 49 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 272 2 24 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 78 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 272 2 23 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 272 2 22 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 272 (accept_3_2 43 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 272 2 21 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 78 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 272 2 20 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 272 2 19 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 78 272 (accept_3_2 37 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 272 2 18 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 272 2 17 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 272 2 16 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 78 272 (accept_3_2 31 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 272 2 15 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 272 (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 78 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 272 2 14 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 272 2 13 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 272 (accept_3_2 25 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 272 2 12 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 272 2 11 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 272 2 10 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 272 (accept_3_2 19 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 272 2 9 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 78 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 272 2 8 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 15
  78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 272 2 7 39 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 272 (accept_3_2 13
  78 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 272 2 6 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 272
  (Polychromatic418967fa.accept_22_11_12_8_1_13645 11 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 272 2 5 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 78 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 272 2 4 39 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 272 (accept_3_2 7 78 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 272 2 3 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 272 2 2 39 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 272 2 1 39 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 272 (accept_3_2 1 78 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 272
  (allA_succ_of_accept 76 77 272 (accept_3_2 76 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 272 (accept_3_2 73 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 272 (Polychromatic418967fa.accept_21_9_14_20_1_4579 72 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 272 (accept_3_2 70 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 272 (Polychromatic418967fa.accept_19_11_1_6_1_5752 68 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 272 (accept_3_2 67 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 77 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 272
  (Polychromatic418967fa.accept_10_5_7_2_1_516 65 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 272 (accept_3_2 64 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 272 (accept_3_2 61 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 272
  (Polychromatic418967fa.accept_10_9_7_2_1_887 59 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 272 (accept_3_2 58 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 272 (Polychromatic418967fa.accept_19_18_1_6_1_5807 56 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 272 (accept_3_2 55 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 77 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 272 (accept_3_2 52 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 272 (accept_3_2 49 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 272
  (Polychromatic418967fa.accept_20_7_17_12_1_11156 47 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 77 272 (accept_3_2 46 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 272 (accept_3_2 43 77 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 42
  77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 272
  (Polychromatic418967fa.accept_14_13_7_6_1_3525 41 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 272 (accept_3_2 40 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 272 (accept_3_2 37 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 272 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 272 (accept_3_2 34 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 272 (Polychromatic418967fa.accept_21_11_14_20_1_12235 32 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 272 (accept_3_2 31 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 272
  (Polychromatic418967fa.accept_10_9_7_2_1_887 29 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 272 (accept_3_2 28 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 272 (accept_3_2 25 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 272
  (Polychromatic418967fa.accept_21_2_14_20_1_841 23 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 272 (accept_3_2 22 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 272 (Polychromatic418967fa.accept_22_20_11_8_1_16662 20 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 272 (accept_3_2 19 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 272 (Polychromatic418967fa.accept_19_18_1_6_1_5807 18 77
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 272 (accept_3_2 16 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 272 (accept_3_2 13 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 272
  (Polychromatic418967fa.accept_19_11_1_6_1_5752 11 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 272 (accept_3_2 10 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 272 (accept_3_2 7 77 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 272
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 272 (accept_3_2 4 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 77 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 272 (accept_3_2 1 77 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 272 (allA_of_3_0 76 76 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 272 (allA_succ_of_accept 74 75
  272 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 272 (accept_3_2 73 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 272 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 272 (accept_3_2 70 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 272 (accept_3_2 67 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 272 (accept_3_2 64 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 272 (accept_3_2 61 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 272 (accept_3_2 58 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 272
  (Polychromatic418967fa.accept_23_10_6_19_1_11862 56 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 75 272 (accept_3_2 55 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 75 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 75 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 272 (accept_3_2 52 75 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 51
  75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 272 (accept_3_2 49 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 272 (accept_3_2 46 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 272 (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 272 (accept_3_2 43 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 272 (accept_3_2 40 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 272 (accept_3_2 37 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 272 (accept_3_2 34 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 272 (accept_3_2 31 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 272 (accept_3_2 28 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 272 (accept_3_2 25 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 272 (accept_3_2 22 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 272
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 272 (accept_3_2 19 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 272 (accept_3_2 16 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 272 (accept_3_2 13 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 272 (accept_3_2 10 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 272 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 75 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 272 (accept_3_2 7 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 272 (accept_3_2 4 75 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 75 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 272 (Polychromatic418967fa.accept_13_2_10_12_1_757
  2 75 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 272 (accept_3_2 1 75
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 272 (allA_succ_of_accept
  73 74 272 (accept_3_2 73 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 272 2 36 37 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 272
  (Polychromatic418967fa.accept_12_11_2_8_1_511 71 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 272 2 35 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 272 (Polychromatic418967fa.accept_19_12_17_6_1_11365 69 74 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 272 2 34 37 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 272 (accept_3_2 67 74 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 272 2 33 37 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 74 272 2 32 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 74 272 (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 74 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 74 272 2 31 37 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 74 272 (accept_3_2 61 74 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74 272 2 30 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 74 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 59
  74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 272 2 29 37 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 272 2 28 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 272 (accept_3_2 55 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 272 2 27 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 74 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 272 2 26 37 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 272 2 25 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 272 (accept_3_2 49 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 272 2 24 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 74 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 272 2 23 37 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 272 2 22 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 272 (accept_3_2 43 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 272 2 21 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 74 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 272 2 20 37 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 272
  (Polychromatic418967fa.accept_21_18_11_20_1_3154 39 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 74 272 2 19 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 74 272 (accept_3_2 37 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 272 2 18 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 74 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 272 2 17 37 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 272 2 16 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 272 (accept_3_2 31 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 272 2 15 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 74 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 272 2 14 37 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 272 2 13 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 272 (accept_3_2 25 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 272 2 12 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 74 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 272 2 11 37 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 272
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 272 2 10 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 272 (accept_3_2 19 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 272 2 9 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 74 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 272 2 8 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 272
  (Polychromatic418967fa.accept_23_15_5_19_1_16661 15 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 74 272 2 7 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 74 272 (accept_3_2 13 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 74 272 2 6 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 74 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 272 2 5 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 74
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 272 2 4 37 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 272 (accept_3_2 7 74
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 272 2 3 37 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 74 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 272 2 2 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 74 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 272 2 1 37 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 272 (accept_3_2 1 74 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  272 (allA_of_3_0 73 73 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 272 (allA_succ_of_accept 71 72 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 272 2 35 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 72 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 72 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 272 4 17 18 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 272 (accept_3_2 67 72 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 272 2 33 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 272 (Polychromatic418967fa.accept_15_5_12_2_1_2820
  65 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 272 8 8 9 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 272
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 272 2 31 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 72 272 (accept_3_2 61 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 272 4 15 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 72 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 272 2 29 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 57
  72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 272 8 7 9 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 272 (accept_3_2 55
  72 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 272 2 27 36 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 272 4 13 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 272 (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 72 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 272 2 25 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 272 (accept_3_2 49 72 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 272 8 6 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 72 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 72 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 272 2 23 36 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 272 4 11 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 272 (accept_3_2 43 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  272 2 21 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 72 272 (Polychromatic418967fa.accept_22_19_6_8_1_10580 41 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 272 8 5 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 72 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 272 2 19 36 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 272 (accept_3_2 37 72 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 272 4 9 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 272 (Polychromatic418967fa.accept_15_5_12_2_1_2820 35 72 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 272 2 17 36 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 272
  (Polychromatic418967fa.accept_15_3_12_2_1_507 33 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 272 8 4 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 272 (accept_3_2 31 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  272 2 15 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 72 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 272 4 7 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 272 (Polychromatic418967fa.accept_21_6_9_20_1_3190 27 72 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 272 2 13 36 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 272 (accept_3_2 25 72 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 272 8 3 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 272 (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 72
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 272 2 11 36 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 272
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 21 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 272 4 5 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 272 (accept_3_2 19 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  272 2 9 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 272 8 2 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 272 2 7 36 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 272 (accept_3_2 13 72 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 272 4 3 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 272 2 5 36 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 272
  (Polychromatic418967fa.accept_19_9_15_6_1_4396 9 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 272 8 1 9 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 272 (accept_3_2 7 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 272
  2 3 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  272 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 72 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 272 4 1 18 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 272 2 1 36 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 272 (accept_3_2 1 72 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 272 (allA_succ_of_accept 70 71 272 (accept_3_2 70 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 71 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 272 (accept_3_2 67 71 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 66
  71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 272 (accept_3_2 64 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 272 (accept_3_2 61 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 272 (accept_3_2 58 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 272 (accept_3_2 55 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 272
  (Polychromatic418967fa.accept_10_3_1_2_1_521 53 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 272 (accept_3_2 52 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 272 (accept_3_2 49 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 272 (accept_3_2 46 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 272 (accept_3_2 43 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 272 (accept_3_2 40 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 272 (accept_3_2 37 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 272
  (Polychromatic418967fa.accept_11_2_5_8_1_470 35 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 272 (accept_3_2 34 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 272 (accept_3_2 31 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 272
  (Polychromatic418967fa.accept_10_9_1_2_1_522 29 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 272 (accept_3_2 28 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 272 (accept_3_2 25 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 272 (accept_3_2 22 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 272 (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 272 (accept_3_2 19 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 272 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 71
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 272
  (Polychromatic418967fa.accept_21_17_8_20_1_7805 17 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 272 (accept_3_2 16 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 272 (accept_3_2 13 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 272
  (Polychromatic418967fa.accept_18_11_17_2_1_6349 11 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 272 (accept_3_2 10 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 272 (Polychromatic418967fa.accept_18_8_17_2_1_1557 8 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 272 (accept_3_2 7 71 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 71 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 272 (accept_3_2 4 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 71 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 272 (accept_3_2 1 71 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 272
  (allA_of_3_0 70 70 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 272 (allA_succ_of_accept 68 69 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 272 (accept_3_2 67 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 272 (accept_3_2 64 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 272 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 272 (accept_3_2 61 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 272 (accept_3_2 58 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 272
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 56 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 272 (accept_3_2 55 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 272 (accept_3_2 52 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 272 (accept_3_2 49 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 272 (accept_3_2 46 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 272 (Polychromatic418967fa.accept_21_3_6_20_1_9278 45 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 272 (accept_3_2 43 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 272 (accept_3_2 40 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 272
  (Polychromatic418967fa.accept_11_5_3_8_1_454 38 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 272 (accept_3_2 37 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 272 (Polychromatic418967fa.accept_19_17_12_6_1_8650 36 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 272 (accept_3_2 34 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 272 (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 272 (accept_3_2 31 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 272 (accept_3_2 28 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 272 (accept_3_2 25 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 272 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 272 (accept_3_2 22 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 272
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 272 (accept_3_2 19 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 272 (accept_3_2 16 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 272 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 272 (accept_3_2 13 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 272 (accept_3_2 10 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 272 (Polychromatic418967fa.accept_21_9_6_20_1_1903 9 69 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 272 (accept_3_2 7 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  272 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 272 (accept_3_2 4 69 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 272 (Polychromatic418967fa.accept_13_2_4_12_1_745 2
  69 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 272 (accept_3_2 1 69 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 272 (allA_succ_of_accept 67 68
  272 (accept_3_2 67 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 272 2 33 34 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 65 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 272 4 16 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 272 (Polychromatic418967fa.accept_24_15_20_8_1_13325 63 68 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 272 2 31 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 272 (accept_3_2 61 68 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 272 4 15 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 272 (Polychromatic418967fa.accept_22_15_2_8_1_13605 59 68
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 272 2 29 34 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 272 4 14 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 272 (accept_3_2 55 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  272 2 27 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 68 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 272 4 13 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 51 68 272 17 3 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 68 272 2 25 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 272 (accept_3_2 49 68 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 68 272 4 12 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 68 272 (Polychromatic418967fa.accept_18_11_14_2_1_5058 47 68 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 272 2 23 34 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 272 4 11 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 68 272 (accept_3_2 43 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68
  272 2 21 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 68 272 (Polychromatic418967fa.accept_13_2_3_12_1_735 41 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 68 272 4 10 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 68 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 68 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 272 2 19 34 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 272 (accept_3_2 37 68 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 272 4 9 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 68 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35
  68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 272 34 1 2 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 272 4 8 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 272 (accept_3_2 31 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  272 2 15 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 68 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 272 4 7 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 68 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 272 2 13 34 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 272 (accept_3_2 25 68 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 272 4 6 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 272 (Polychromatic418967fa.accept_21_2_5_20_1_7789 23 68 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 272 2 11 34 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 272 4 5 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 272 (accept_3_2 19 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  272 2 9 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 68
  272 17 1 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 16 68
  272 4 4 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  68 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 68 272 2 7 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 68 272 (accept_3_2 13 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 68 272 4 3 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 68 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 272 2 5 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 272 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9
  68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 272 4 2 17 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 272 (accept_3_2 7 68
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 272 2 3 34 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 68 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 272 4 1 17 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 68 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 272 2 1 34 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 272 (accept_3_2 1 68 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 272
  (allA_of_3_0 67 67 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 272 (allA_succ_of_accept 65 66 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 272 2 32 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 272 2 31 33 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 272 (accept_3_2 61 66 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 272 2 30 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 59
  66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 272 2 29 33 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 272 2 28 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 272 (accept_3_2 55 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 272 2 27 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 66 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 272 2 26 33 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 272 2 25 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 272 (accept_3_2 49 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 272 2 24 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 272 (Polychromatic418967fa.accept_13_8_1_12_1_762 47 66 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 272 2 23 33 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 272 2 22 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 272 (accept_3_2 43 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 272 2 21 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 66 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 272 2 20 33 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 272 2 19 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 272 (accept_3_2 37 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 272 2 18 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 272 2 17 33 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 272 2 16 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 272 (accept_3_2 31 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 272 2 15 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 272 (Polychromatic418967fa.accept_19_10_9_6_1_13992 29 66 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 272 2 14 33 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 272 2 13 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 272 (accept_3_2 25 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 272 2 12 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 272 2 11 33 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 272 2 10 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 272 (accept_3_2 19 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 272 2 9 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 272 2 8 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 272 2 7 33 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 272 (accept_3_2 13
  66 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 272 2 6 33 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 272 2 5 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 272 2 4 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 272 (accept_3_2 7 66 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 272 2 3 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 66 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 272 2 2 33 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  66 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 272 2 1 33 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 272 (accept_3_2 1 66
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 272 (allA_succ_of_accept 64 65 272
  (accept_3_2 64 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 65 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 272 (accept_3_2 61 65 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 272 (accept_3_2 58 65
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 272
  (Polychromatic418967fa.accept_15_11_5_2_1_520 56 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 272 (accept_3_2 55 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 272 (Polychromatic418967fa.accept_19_16_8_6_1_4407 54 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 272 (accept_3_2 52 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 272 (accept_3_2 49 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 47 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 272 (accept_3_2 46 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 272
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 44 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 272 (accept_3_2 43 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 272 (accept_3_2 40 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 272 (accept_3_2 37 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 272 (Polychromatic418967fa.accept_18_17_11_2_1_7782 35 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 272 (accept_3_2 34 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 272 (accept_3_2 31 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 272 (Polychromatic418967fa.accept_20_10_5_12_1_13866 30 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 272 (accept_3_2 28 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 272 (accept_3_2 25 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 272 (accept_3_2 22 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 272
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 272 (accept_3_2 19 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 272 (accept_3_2 16 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 272 (accept_3_2 13 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 272 (Polychromatic418967fa.accept_15_12_5_2_1_2786 12 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 272 (accept_3_2 10 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 272 (accept_3_2 7 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  272 (Polychromatic418967fa.accept_20_6_5_12_1_8169 6 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 65 272 (Polychromatic418967fa.accept_21_5_2_20_1_6081 5 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 272 (accept_3_2 4 65 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 272 (accept_3_2 1 65 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 272 (allA_of_3_0 64 64 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 272 (allA_succ_of_accept 62 63 272
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 62 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 63 272 (accept_3_2 61 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 272 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 272 (accept_3_2 58 63 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 272 (Polychromatic418967fa.accept_14_1_7_6_1_3604
  57 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 272
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 56 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 272 (accept_3_2 55 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 272 (accept_3_2 52 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 63 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 272
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 272 (accept_3_2 49 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 272 (Polychromatic418967fa.accept_23_2_17_19_1_10370 48 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 272 (accept_3_2 46 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 63 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 272
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 44 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 272 (accept_3_2 43 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 272 (accept_3_2 40 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 39 63 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 272
  (Polychromatic418967fa.accept_22_16_19_8_1_16660 38 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 63 272 (accept_3_2 37 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 63 272 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 272 (accept_3_2 34 63 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 272
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 272 (Polychromatic418967fa.accept_22_10_19_8_1_8983 32 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 272 (accept_3_2 31 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 272 (accept_3_2 28 63
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 272
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 272 (Polychromatic418967fa.accept_24_2_15_8_1_6377 26 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 272 (accept_3_2 25 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 272 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23
  63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 272 (accept_3_2 22 63
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 272
  (Polychromatic418967fa.accept_10_1_3_2_1_220 21 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 272 (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 272 (accept_3_2 19 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17
  63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 272 (accept_3_2 16 63
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 272
  (Polychromatic418967fa.accept_10_5_3_2_1_899 15 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 272 (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 272 (accept_3_2 13 63 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 272 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 63 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 272 (accept_3_2 10 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  63 272 (Polychromatic418967fa.accept_20_9_3_12_1_6627 9 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 63 272 (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 272 (accept_3_2 7 63 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 272 (accept_3_2 4 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63
  272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 3 63 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 63 272 (Polychromatic418967fa.accept_23_2_17_19_1_10370 2 63 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 272 (accept_3_2 1 63 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 62 272 (allA_succ_of_accept 61 62 272 (accept_3_2 61 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 62 272 2 30 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 62 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 62 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 62 272 2 29 31 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 62 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 62 272 2 28 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 62 272 (accept_3_2 55 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 62 272 2 27 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 62 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 62 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 272 2 26 31 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 272 2 25 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 272 (accept_3_2 49 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 272 2 24 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 62 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 272 2 23 31 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 272
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 272 2 22 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 272 (accept_3_2 43 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 272 2 21 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 272 2 20 31 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 272 2 19 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 272 (accept_3_2 37 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 272 2 18 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 272 2 17 31 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 272 2 16 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 272 (accept_3_2 31 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 272 2 15 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 62 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 272 2 14 31 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 272
  (Polychromatic418967fa.accept_20_7_2_12_1_6642 27 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 272 2 13 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 272 (accept_3_2 25 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 272 2 12 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 62 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 272 2 11 31 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 272 2 10 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 272 (accept_3_2 19 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 272 2 9 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 62 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 272 2 8 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  62 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 272 2 7 31 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 272 (accept_3_2 13
  62 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 272 2 6 31 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 272
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 62 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 272 2 5 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 272 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 62 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 272 2 4 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 272 (accept_3_2 7 62 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 272 2 3 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 272 2 2 31 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 62
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 272 2 1 31 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 272 (accept_3_2 1 62
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 272 (allA_of_3_0 61 61 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 272 (allA_succ_of_accept 59 60 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 272 2 29 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 272 4 14 15 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 272 (accept_3_2 55 60 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 272 2 27 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 53
  60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 272 4 13 15 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 272 2 25 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 60 272 (accept_3_2 49 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 272 4 12 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 272 2 23 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 45
  60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 272 4 11 15 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 272 (accept_3_2 43
  60 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 272 2 21 30 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 272 4 10 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 272 2 19 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 272 (accept_3_2 37 60 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 272 4 9 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 60 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 272 2 17 30 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 272 4 8 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 272 (accept_3_2 31 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  272 2 15 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 60 272 (Polychromatic418967fa.accept_22_7_16_8_1_13587 29 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 272 4 7 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 272 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 60 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 272 2 13 30 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 272 (accept_3_2 25 60 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 272 4 6 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 272 2 11 30 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 272 4 5 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 272 (accept_3_2 19 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  272 2 9 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 272 4 4 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 272 (Polychromatic418967fa.accept_21_15_18_20_1_9292 15 60 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 272 2 7 30 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 272 (accept_3_2 13 60 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 272 4 3 15 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 272
  (Polychromatic418967fa.accept_21_11_18_20_1_1877 11 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 272 2 5 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 60 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 272 4 2 15 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 272 (accept_3_2 7 60 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 272 2 3 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 272 4 1 15 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 272 2 1 30 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 272 (accept_3_2 1 60 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 272 (allA_succ_of_accept 58 59 272
  (accept_3_2 58 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 59 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 272 (accept_3_2 55 59 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 272 (Polychromatic418967fa.accept_25_4_9_22_1_16659 54 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 272 (accept_3_2 52 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 272 (accept_3_2 49 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 272
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 272 (accept_3_2 46 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 272 (accept_3_2 43 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 272
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 272 (accept_3_2 40 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 272 (accept_3_2 37 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 272 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 272 (accept_3_2 34 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 272 (accept_3_2 31 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 272
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 272 (accept_3_2 28 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 272 (accept_3_2 25 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 272 (accept_3_2 22 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 272 (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 272 (accept_3_2 19 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 272 (accept_3_2 16 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 272 (accept_3_2 13 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 272 (accept_3_2 10 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 272 (accept_3_2 7 59 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 59 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 272
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 272 (accept_3_2 4 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 272 (accept_3_2 1 59 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 272 (allA_of_3_0
  58 58 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 272 (allA_succ_of_accept 56 57 272
  (Polychromatic418967fa.accept_13_4_5_12_1_751 56 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 272 (accept_3_2 55 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 272 (accept_3_2 52 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 57 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 272 (accept_3_2 49 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 272 (accept_3_2 46 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 57 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 272 (accept_3_2 43 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 272 (accept_3_2 40 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 57 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 272
  (Polychromatic418967fa.accept_11_5_2_8_1_866 38 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 272 (accept_3_2 37 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 272 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 272 (accept_3_2 34 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 272 (accept_3_2 31 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 272 (accept_3_2 28 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 57 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 272 (accept_3_2 25 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 272 (accept_3_2 22 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 272 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 57 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 272
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 272 (accept_3_2 19 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 272 (accept_3_2 16 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 272 (accept_3_2 13 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 272 (accept_3_2 10 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 272 (accept_3_2 7 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 272 (accept_3_2 4 57 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 57 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  57 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 272 (accept_3_2 1 57 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 272 (allA_succ_of_accept 55 56 272 (accept_3_2 55 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 272 2 27 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 56 272 (Polychromatic418967fa.accept_21_11_14_20_1_12235 53 56 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 272 4 13 14 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 56 272 2 25 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 56 272 (accept_3_2 49 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 56 272 8 6 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 56 272 (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 56 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 272 2 23 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 272 (Polychromatic418967fa.accept_19_7_18_6_1_3095
  45 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 272 4 11 14 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 272 (accept_3_2 43
  56 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 272 2 21 28 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 56 272 8 5 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 56 272 (Polychromatic418967fa.accept_15_9_11_2_1_1882 39 56 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 272 2 19 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 272 (accept_3_2 37 56 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 272 4 9 14 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 56 272 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 56 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 272 2 17 28 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 272
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 272 8 4 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 272 (accept_3_2 31 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  272 2 15 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 56 272 (Polychromatic418967fa.accept_13_3_4_12_1_36 29 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 272 4 7 14 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 272 (Polychromatic418967fa.accept_21_6_14_20_1_4594 27 56 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 272 2 13 28 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 272 (accept_3_2 25 56 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 272 8 3 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 272 (Polychromatic418967fa.accept_21_2_14_20_1_841
  23 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 272 2 11 28 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 272 4 5 14 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 272 (accept_3_2 19 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  272 2 9 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 272 (Polychromatic418967fa.accept_19_17_18_6_1_7192 17 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 272 8 2 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 56 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 272 2 7 28 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 272 (accept_3_2 13 56 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 272 4 3 14 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 56 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 272 2 5 28 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 272
  (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 272 8 1 7 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 272 (accept_3_2 7 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 272
  2 3 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  272 (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 56 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 56 272 4 1 14 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 56 272 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 56 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 272 2 1 28 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 272 (accept_3_2 1 56 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 56 272)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 272
  (allA_of_3_0 55 55 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 272 (allA_succ_of_accept 53 54 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 272 2 26 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 54 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 54 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 272 2 25 27 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 272 (accept_3_2 49 54 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 272 2 24 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 47
  54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 272 2 23 27 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 272 2 22 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 54 272 (accept_3_2 43 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 272 2 21 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 54 272 (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 54 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 272 2 20 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 272 2 19 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 54 272 (accept_3_2 37 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 272 2 18 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 272 (Polychromatic418967fa.accept_23_12_8_19_1_16658 35 54 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 272 2 17 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 272 2 16 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 54 272 (accept_3_2 31 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 272 2 15 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 272 2 14 27 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 272 2 13 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 272 (accept_3_2 25 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 272 2 12 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 272 (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 54 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 272 2 11 27 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 272 2 10 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 272 (accept_3_2 19 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 272 2 9 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 54 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 272 2 8 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 272 2 7 27 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 272 (accept_3_2 13
  54 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 272 2 6 27 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 272 2 5 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 54 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 272 2 4 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 272 (accept_3_2 7 54 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 272 2 3 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 54 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 272 2 2 27 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  54 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 272 2 1 27 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 272 (accept_3_2 1 54
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 272))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 272 (allA_succ_of_accept 52 53 272 (accept_3_2 52 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 53 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 272 (accept_3_2 49 53 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48
  53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 272 (accept_3_2 46 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 272 (accept_3_2 43 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 272 (accept_3_2 40 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 272 (accept_3_2 37 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 272 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 53 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 272
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 272 (accept_3_2 34 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 272 (accept_3_2 31 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 272
  (Polychromatic418967fa.accept_18_11_17_2_1_6349 29 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 272 (accept_3_2 28 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 272 (accept_3_2 25 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 272 (accept_3_2 22 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 272 (Polychromatic418967fa.accept_27_20_26_2_1_16657 20 53 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 272 (accept_3_2 19 53 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 272 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 53 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 272 (accept_3_2 16 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 272 (accept_3_2 13 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 272
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 272 (accept_3_2 10 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 272 (Polychromatic418967fa.accept_13_8_1_12_1_762 8 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 272 (accept_3_2 7 53 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 53 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 272 (accept_3_2 4 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 53 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 272 (accept_3_2 1 53 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 272))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 272 (allA_of_3_0 52 52
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 272 (allA_succ_of_accept 50 51 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 272 (accept_3_2 49 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 272 (accept_3_2 46 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 272 (accept_3_2 43 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 272 (accept_3_2 40 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 272 (accept_3_2 37 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 51 272 17 2 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 51 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 33
  51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 272 (accept_3_2 31 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 272 (accept_3_2 28 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 272 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 51 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 272 (accept_3_2 25 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 272 (accept_3_2 22 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 272
  (Polychromatic418967fa.accept_24_20_3_8_1_9889 20 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 272 (accept_3_2 19 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 17 51 272 17 1 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 16 51 272 (accept_3_2 16 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 51 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 51 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 272 (accept_3_2 13 51 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12
  51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 272 (accept_3_2 10 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 51 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 272 (accept_3_2 7 51 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 51 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 272 (accept_3_2 4 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 272 (Polychromatic418967fa.accept_19_2_13_6_1_1978 2 51 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 272 (accept_3_2 1 51 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 272))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 272 (allA_succ_of_accept
  49 50 272 (accept_3_2 49 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 272 2 24 25 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 272 2 23 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 50 272 (Polychromatic418967fa.accept_20_5_10_12_1_8200 45 50 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 272 2 22 25 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 272 (accept_3_2 43 50 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 272 2 21 25 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 272
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 272 2 20 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 50 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 50 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 272 2 19 25 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 272 (accept_3_2 37 50 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 272 2 18 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35
  50 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 272 2 17 25 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 272 2 16 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 272 (accept_3_2 31 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 272 2 15 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 272 2 14 25 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 272
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 272 2 13 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 272 (accept_3_2 25 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 272 2 12 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 272 2 11 25 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 272 2 10 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 272 (accept_3_2 19 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 272 2 9 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 50 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 272 2 8 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  50 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 272 2 7 25 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 272 (accept_3_2 13
  50 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 272 2 6 25 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 272
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 50 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 272 2 5 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 50 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 272 2 4 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 272 (accept_3_2 7 50 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 272 2 3 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 50 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 272 2 2 25 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 50
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 272 2 1 25 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 272 (accept_3_2 1 50
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 272))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 272 (allA_of_3_0 49 49 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 272
  (allA_succ_of_accept 47 48 272 (Polychromatic418967fa.accept_13_8_9_12_1_2813 47 48 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 272 2 23 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 45
  48 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 272 4 11 12 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 272 (accept_3_2 43
  48 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 272 2 21 24 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 272 8 5 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 48 272 (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 48 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 272 2 19 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 272 (accept_3_2 37 48 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 272 4 9 12 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 48 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 272 2 17 24 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 272 16 2 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 272 (accept_3_2 31 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  272 2 15 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 48 272 (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 272 4 7 12 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 272 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 48 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 272 2 13 24 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 272 (accept_3_2 25 48 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 272 8 3 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 272 2 11 24 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 272
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 272 4 5 12 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 272 (accept_3_2 19 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  272 2 9 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 272 16 1 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 272 2 7 24 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 272 (accept_3_2 13 48 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 272 4 3 12 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 272 (Polychromatic418967fa.accept_21_11_6_20_1_4589 11 48
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 272 2 5 24 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 272
  (Polychromatic418967fa.accept_19_9_10_6_1_4394 9 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 272 8 1 6 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 272 (accept_3_2 7 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 272
  2 3 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 272 4 1 12 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 272 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 48 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 272 2 1 24 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 272 (accept_3_2 1 48 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 272)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 272 (allA_succ_of_accept 46
  47 272 (accept_3_2 46 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 47 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 272 (accept_3_2 43 47 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 272 (Polychromatic418967fa.accept_20_2_7_12_1_5215 42 47 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 272
  (Polychromatic418967fa.accept_14_13_5_6_1_2747 41 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 272 (accept_3_2 40 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 38 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 272 (accept_3_2 37 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 272
  (Polychromatic418967fa.accept_10_5_7_2_1_516 35 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 272 (accept_3_2 34 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 272 (accept_3_2 31 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 272 (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 47 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 272 (accept_3_2 28 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 272 (accept_3_2 25 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 47 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 272
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 272 (accept_3_2 22 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 272 (Polychromatic418967fa.accept_13_7_8_12_1_2810 20 47 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 272 (accept_3_2 19 47 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 272
  (Polychromatic418967fa.accept_11_6_3_8_1_843 17 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 272 (accept_3_2 16 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 272 (accept_3_2 13 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 272 (Polychromatic418967fa.accept_24_12_23_8_1_13335 12 47 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 272 (accept_3_2 10 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 272 (accept_3_2 7 47 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 47 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 272
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 272 (accept_3_2 4 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 47 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 272 (accept_3_2 1 47 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 272))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 272 (allA_of_3_0 46 46 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 272 (allA_succ_of_accept 44 45 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 272 (accept_3_2 43 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 272 (accept_3_2 40 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 45 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 272 (accept_3_2 37 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 272 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 272 (accept_3_2 34 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 45 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 272 (accept_3_2 31 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 272 (accept_3_2 28 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 45 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 272
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 272 (accept_3_2 25 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 272 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 272 (accept_3_2 22 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 21 45 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 272
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 272 (accept_3_2 19 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 272 (accept_3_2 16 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 45 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 272
  (Polychromatic418967fa.accept_19_14_7_6_1_8654 14 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 272 (accept_3_2 13 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 272 (Polychromatic418967fa.accept_21_12_3_20_1_4567 12 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 272 (accept_3_2 10 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 272 (accept_3_2 7 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 45 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 272 (accept_3_2 4 45 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 45 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 45
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 272 (accept_3_2 1 45 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 272))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  272 (allA_succ_of_accept 43 44 272 (accept_3_2 43 44 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 272 2 21 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 44 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 272 4 10 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 39
  44 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 272 2 19 22 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 272 (accept_3_2 37
  44 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 272 4 9 11 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 272
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 44 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 272 2 17 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 44 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 44 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 272 4 8 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 272 (accept_3_2 31 44 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 272 2 15 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 272 4 7 11 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 44 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 272 2 13 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 272 (accept_3_2 25 44 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 272 4 6 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 44 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 272 2 11 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 21
  44 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 272 4 5 11 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 272 (accept_3_2 19
  44 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 272 2 9 22 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 44 272 4 4 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 44 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 44 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 272 2 7 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 272 (accept_3_2 13 44 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 272 4 3 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 272 2 5 22 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 272
  (Polychromatic418967fa.accept_21_9_2_20_1_857 9 44 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 272 4 2 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 272 (accept_3_2 7 44 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 272
  2 3 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 272 4 1 11 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 272 2 1 22 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 272 (accept_3_2 1 44 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 272)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 272 (allA_of_3_0 43 43 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 272 (allA_succ_of_accept 41 42 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 272 2 20 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 272 2 19 21 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 272 (accept_3_2 37 42 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 272 2 18 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35
  42 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 272 2 17 21 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 272 2 16 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 272 (accept_3_2 31 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 272 2 15 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 272 (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 42 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 272 2 14 21 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 272 2 13 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 272 (accept_3_2 25 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 272 2 12 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 272 2 11 21 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 272 2 10 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 42 272 (accept_3_2 19 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 272 2 9 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 272 2 8 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  42 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 272 2 7 21 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 272 (accept_3_2 13
  42 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 272 2 6 21 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 272
  (Polychromatic418967fa.accept_22_11_20_8_1_13603 11 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 42 272 2 5 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 42 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 272 2 4 21 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 272 (accept_3_2 7 42 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 272 2 3 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 272 2 2 21 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 272 2 1 21 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 272 (accept_3_2 1 42 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  272)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 272 (allA_succ_of_accept 40 41 272 (accept_3_2 40 41 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 272 (accept_3_2 37 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 41 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 272 (accept_3_2 34 41 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 272
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 32 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 272 (accept_3_2 31 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 41 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 272 (accept_3_2 28 41 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 272 (accept_3_2 25 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 23 41 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 272 (accept_3_2 22 41 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 272
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 272 (accept_3_2 19 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 272 (accept_3_2 16 41 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 272 (accept_3_2 13 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 272 (Polychromatic418967fa.accept_20_11_1_12_1_3803 11 41 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 272 (accept_3_2 10 41 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 272 (accept_3_2 7 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 41 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 272 (accept_3_2 4 41 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  41 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 272 (accept_3_2 1 41 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 272))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 272
  (allA_of_3_0 40 40 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 272 (allA_succ_of_accept 38 39 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 272 (accept_3_2 37 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 272 (accept_3_2 34 39 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 272 (accept_3_2 31 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 272 (accept_3_2 28 39 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 39 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 272 (accept_3_2 25 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 272 (accept_3_2 22 39 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 39 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 272
  (Polychromatic418967fa.accept_23_20_16_19_1_16656 20 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 39 272 (accept_3_2 19 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 272 (accept_3_2 16 39 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 272 (accept_3_2 13 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 272 (accept_3_2 10 39 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 272 (accept_3_2 7 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 272 (accept_3_2 4 39 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  39 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 272 (accept_3_2 1 39 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 272))))))))))))))))))))))))))))))))))))))) (allB_succ 38 272
  (allA_succ_of_accept 37 38 272 (accept_3_2 37 38 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  272 2 18 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 38 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 272 2 17 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 272 (Polychromatic418967fa.accept_23_10_15_19_1_10261 33 38 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 272 2 16 19 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 272 (accept_3_2 31
  38 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 272 2 15 19 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 272
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 38 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 272 2 14 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 272 (Polychromatic418967fa.accept_23_4_15_19_1_10311 27 38 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 272 2 13 19 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 272 (accept_3_2 25 38 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 272 2 12 19 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 38 272 2 11 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 38 272 (Polychromatic418967fa.accept_15_6_8_2_1_104 21 38 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 38 272 2 10 19 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 38 272 (accept_3_2 19 38 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38 272 2 9 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 38 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  38 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 272 2 8 19 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 38 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 38 272 2 7 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 38 272 (accept_3_2 13 38 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38
  272 2 6 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  38 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 38 272 2 5 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 38 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 38 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 272 2 4 19 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 272 (accept_3_2 7 38 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 272 2 3 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 38 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 272 2 2 19 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 272
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 38 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 38 272 2 1 19 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 38 272 (accept_3_2 1 38 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38
  272)))))))))))))))))))))))))))))))))))))) (allB_succ 37 272 (allA_of_3_0 37 37 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 36 272 (allA_succ_of_accept 35 36 272 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 36 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 272 2 17 18 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 272 4 8 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 272 (accept_3_2 31 36 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36
  272 2 15 18 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 36 272 (Polychromatic418967fa.accept_23_6_13_19_1_10304 29 36 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 36 272 4 7 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 36 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 36 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 272 2 13 18 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 272 (accept_3_2 25 36 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 272 4 6 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 272 2 11 18 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 36 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 36 272 4 5 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 36 272 (accept_3_2 19 36 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36
  272 2 9 18 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  36 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 36 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 36 272 4 4 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 36 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 36 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 272 2 7 18 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 272 (accept_3_2 13 36 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 272 4 3 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 36 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 272 2 5 18 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 272 4 2 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 272 (accept_3_2 7 36 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 272
  2 3 18 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36
  272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 272 4 1 9 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 36 272 (Polychromatic418967fa.accept_19_3_17_6_1_1991 3 36 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 272 2 1 18 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 272 (accept_3_2 1 36 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 272)))))))))))))))))))))))))))))))))))) (allB_succ 35 272 (allA_succ_of_accept 34 35 272
  (accept_3_2 34 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 272 (accept_3_2 31 35 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 272 (Polychromatic418967fa.accept_13_3_9_12_1_2062
  29 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 272 (accept_3_2 28
  35 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 35 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 272 (accept_3_2 25 35 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23
  35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 272 (accept_3_2 22 35
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 272 (Polychromatic418967fa.accept_6_3_5_2_1_12
  21 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 272
  (Polychromatic418967fa.accept_27_20_8_2_1_16655 20 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 272 (accept_3_2 19 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 35 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 272 (accept_3_2 16 35 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 272 (accept_3_2 13 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 35 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 272 (accept_3_2 10 35 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 272 (accept_3_2 7 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 35 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 272 (accept_3_2 4 35 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  35 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 272 (accept_3_2 1 35 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 272))))))))))))))))))))))))))))))))))) (allB_succ 34 272
  (allA_of_3_0 34 34 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 272 (allA_succ_of_accept 32 33 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 272 (accept_3_2 31 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 272 (accept_3_2 28 33 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 272 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 33 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 272 (accept_3_2 25 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 272 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 272 (accept_3_2 22 33 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 272
  (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 272 (accept_3_2 19 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 272 (accept_3_2 16 33 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 272 (accept_3_2 13 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 272 (accept_3_2 10 33 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 272 (Polychromatic418967fa.accept_19_9_14_6_1_2014 9 33 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 272 (accept_3_2 7 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 272 (accept_3_2 4 33 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 33 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 272 (Polychromatic418967fa.accept_22_2_11_8_1_13586
  2 33 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 272 (accept_3_2 1 33
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 272))))))))))))))))))))))))))))))))) (allB_succ 32 272
  (allA_succ_of_accept 31 32 272 (accept_3_2 31 32 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  272 2 15 16 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 32 272 (Polychromatic418967fa.accept_18_11_14_2_1_5058 29 32 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 272 4 7 8 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 272 (Polychromatic418967fa.accept_19_8_13_6_1_7153 27 32 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 272 2 13 16 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 272 (accept_3_2 25 32 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 272 8 3 4 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 32 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 272 2 11 16 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 32 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 272 4 5 8 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 272 (accept_3_2 19 32 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  272 2 9 16 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 272 16 1 2 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 32 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 272 2 7 16 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 272 (accept_3_2 13 32 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 272 4 3 8 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 272 (Polychromatic418967fa.accept_18_11_14_2_1_5058 11 32
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 272 2 5 16 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 272 8 1 4 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 272 (accept_3_2 7 32 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 272
  2 3 16 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 272 4 1 8 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 272 2 1 16 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 272 (accept_3_2 1 32 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 272)))))))))))))))))))))))))))))))) (allB_succ 31 272 (allA_of_3_0 31 31 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 272 (allA_succ_of_accept 29 30 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 272 2 14 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 30 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 272 2 13 15 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 272 (accept_3_2 25 30 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 272 2 12 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 23
  30 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 272 2 11 15 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 272 2 10 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 272 (accept_3_2 19 30 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 272 2 9 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 30 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 272 2 8 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  30 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 272 2 7 15 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 272 (accept_3_2 13
  30 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 272 2 6 15 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 272 2 5 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 272 2 4 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 272 (accept_3_2 7 30 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 272 2 3 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 30 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 272 2 2 15 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 272 2 1 15 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 272 (accept_3_2 1 30
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 272)))))))))))))))))))))))))))))) (allB_succ 29 272
  (allA_succ_of_accept 28 29 272 (accept_3_2 28 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 29 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 272 (accept_3_2 25 29 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 272 (Polychromatic418967fa.accept_28_24_1_20_1_16654 24 29 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 272 (accept_3_2 22 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 272 (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 29 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 272 (accept_3_2 19 29 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 272 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 29
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 272
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 272 (accept_3_2 16 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 29 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 272 (accept_3_2 13 29 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 272
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 272 (accept_3_2 10 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 272 (Polychromatic418967fa.accept_25_8_4_22_1_16653 8 29 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 272 (accept_3_2 7 29 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 272 (Polychromatic418967fa.accept_24_6_5_8_1_16652 6 29 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 272 (accept_3_2 4 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 29 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 272 (accept_3_2 1 29 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 272))))))))))))))))))))))))))))) (allB_succ 28 272 (allA_of_3_0 28 28 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 272 (allA_succ_of_accept 26 27 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140
  26 27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 272 (accept_3_2 25
  27 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 272
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 272 (accept_3_2 22 27 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 272 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 27 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 272 (Polychromatic418967fa.accept_15_5_12_2_1_2820
  20 27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 272 (accept_3_2 19
  27 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 272
  (Polychromatic418967fa.accept_12_6_3_8_1_512 18 27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 272 (accept_3_2 16 27 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 27 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 272 (Polychromatic418967fa.accept_10_4_7_2_1_211
  14 27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 272 (accept_3_2 13
  27 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 272
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 272 (accept_3_2 10 27 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 27 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 272 (Polychromatic418967fa.accept_13_8_1_12_1_762 8
  27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 272 (accept_3_2 7 27 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6
  27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 272 (accept_3_2 4 27 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  272 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 27 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 27 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 272 (accept_3_2 1 27 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 272))))))))))))))))))))))))))) (allB_succ 26 272 (allA_succ_of_accept 25 26 272 (accept_3_2
  25 26 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 272 2 12 13 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 26 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 272 2 11 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 26 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 26 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 272 2 10 13 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 272 (accept_3_2 19 26 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 272 2 9 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  26 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 272 2 8 13 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 26 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 272 2 7 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 272 (accept_3_2 13 26 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  272 2 6 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 272 2 5 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 26 272 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 26 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 272 2 4 13 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 272 (accept_3_2 7 26 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 272 2 3 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 272 2 2 13 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 26 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 272 2 1 13 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 272 (accept_3_2 1 26 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  272)))))))))))))))))))))))))) (allB_succ 25 272 (allA_of_3_0 25 25 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 272 (allA_succ_of_accept 23 24 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 272 2 11 12 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 272 4 5 6 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 272 (accept_3_2 19 24 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  272 2 9 12 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 272 8 2 3 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 272 (Polychromatic418967fa.accept_19_15_5_6_1_5760 15 24 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 272 2 7 12 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 272 (accept_3_2 13 24 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 272 4 3 6 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 272 2 5 12 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 272 8 1 3 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 272 (accept_3_2 7 24 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 272
  2 3 12 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 272 4 1 6 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 272 2 1 12 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 272 (accept_3_2 1 24 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 272)))))))))))))))))))))))) (allB_succ 23 272 (allA_succ_of_accept 22 23 272 (accept_3_2 22
  23 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 272 (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 23 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 272 (accept_3_2 19 23 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  23 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 272 (accept_3_2 16 23
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 272 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 272 (accept_3_2 13 23 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 272 (accept_3_2 10 23 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 272 (accept_3_2 7 23 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 23 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 23 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 272 (accept_3_2 4 23 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  23 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 272 (accept_3_2 1 23 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 272))))))))))))))))))))))) (allB_succ 22 272 (allA_of_3_0 22 22
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 272 (allA_succ_of_accept 20 21 272
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 272 (accept_3_2 19 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 272 (accept_3_2 16 21 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 272 (accept_3_2 13 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 272 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 272 (accept_3_2 10 21 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 21 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 272 (accept_3_2 7 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 272 (accept_3_2 4 21 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 21 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 272 (Polychromatic418967fa.accept_22_2_21_8_1_16651
  2 21 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 272 (accept_3_2 1 21
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 272))))))))))))))))))))) (allB_succ 20 272
  (allA_succ_of_accept 19 20 272 (accept_3_2 19 20 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20
  272 2 9 10 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  20 272 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 20 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 272 4 4 5 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 20 272 (Polychromatic418967fa.accept_23_15_20_19_1_10274 15 20 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 272 2 7 10 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 272 (accept_3_2 13 20 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 272 4 3 5 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 272 (Polychromatic418967fa.accept_13_11_7_12_1_2758
  11 20 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 272 2 5 10 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 272
  (Polychromatic418967fa.accept_24_9_20_8_1_9900 9 20 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 272 4 2 5 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 272 (accept_3_2 7 20 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 272
  2 3 10 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  272 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 20 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 20 272 4 1 5 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 20 272 (Polychromatic418967fa.accept_15_3_5_2_1_2816 3 20 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 272 2 1 10 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 272 (accept_3_2 1 20 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 20 272)))))))))))))))))))) (allB_succ 19 272 (allA_of_3_0 19 19 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 18 272 (allA_succ_of_accept 17 18 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  18 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 272 2 8 9 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 18 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 272 2 7 9 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 272 (accept_3_2 13 18 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  272 2 6 9 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 272 (Polychromatic418967fa.accept_19_11_18_6_1_3113 11 18 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 272 2 5 9 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 272 2 4 9 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 272 (accept_3_2 7 18 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 272 2 3 9 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 272 2 2 9 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 272 2 1 9 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 272 (accept_3_2 1 18 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  272)))))))))))))))))) (allB_succ 17 272 (allA_succ_of_accept 16 17 272 (accept_3_2 16 17 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 272 (accept_3_2 13 17 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 17 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 272 (accept_3_2 10 17 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 272
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 17 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 272 (accept_3_2 7 17 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 17 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 272 (accept_3_2 4 17 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 17
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 272 (accept_3_2 1 17 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 272))))))))))))))))) (allB_succ 16 272 (allA_of_3_0 16 16 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 272 (allA_succ_of_accept 14 15 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 15 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 272 (accept_3_2 13 15 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 272 (accept_3_2 10 15 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 15 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 15 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 272 (accept_3_2 7 15 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 15 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 272 (accept_3_2 4 15 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 15 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  15 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 272 (accept_3_2 1 15 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 272))))))))))))))) (allB_succ 14 272 (allA_succ_of_accept 13 14
  272 (accept_3_2 13 14 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 272 2 6 7 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 272
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 272 2 5 7 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 272 (Polychromatic418967fa.accept_19_9_14_6_1_2014 9 14 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 272 2 4 7 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 272 (accept_3_2 7 14 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 272 2 3 7 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 14 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 272 2 2 7 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 14
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 272 2 1 7 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 272 (accept_3_2 1 14
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 272)))))))))))))) (allB_succ 13 272 (allA_of_3_0 13 13 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 272 (allA_succ_of_accept 11 12 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 272 2 5 6 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 272 (Polychromatic418967fa.accept_21_9_12_20_1_10792 9 12 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 272 4 2 3 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 272 (accept_3_2 7 12 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 272 2 3 6 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 272 4 1 3 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 3
  12 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 272 2 1 6 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 272 (accept_3_2 1 12
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 272)))))))))))) (allB_succ 11 272 (allA_succ_of_accept 10 11
  272 (accept_3_2 10 11 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 272 (Polychromatic418967fa.accept_21_8_11_20_1_4574 8 11 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 272 (accept_3_2 7 11 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 11 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  11 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 272 (accept_3_2 4 11 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 11 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 272 (accept_3_2 1 11 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  272))))))))))) (allB_succ 10 272 (allA_of_3_0 10 10 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 272
  (allA_succ_of_accept 8 9 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 272 (accept_3_2 7 9 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 9 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 272 (accept_3_2 4 9 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 272
  (Polychromatic418967fa.accept_20_2_9_12_1_2546 2 9 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 272 (accept_3_2 1 9 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 272)))))))))
  (allB_succ 8 272 (allA_succ_of_accept 7 8 272 (accept_3_2 7 8 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 272 2 3 4 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 272 4 1 2 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 8 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 272 2 1 4 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 272 (accept_3_2 1 8 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 272)))))))) (allB_succ 7 272 (allA_of_3_0 7 7 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 272 (allA_succ_of_accept 5 6 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 272 2 2 3 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 6 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 272 2 1 3 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 272 (accept_3_2 1 6 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 272))))))
  (allB_succ 5 272 (allA_succ_of_accept 4 5 272 (accept_3_2 4 5 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 5 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 272 (accept_3_2 1 5 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 272))))) (allB_succ 4 272 (allA_of_3_0 4 4 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 272 (allA_succ_of_accept 2 3 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 272 (accept_3_2 1 3 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 272))) (allB_succ 2 272 (allA_succ_of_accept 1 2 272 (accept_3_2 1 2 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 272)) (allB_two
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


