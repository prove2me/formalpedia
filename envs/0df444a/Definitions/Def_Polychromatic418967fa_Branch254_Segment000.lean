-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch254_Segment000
-- name    : Polychromatic418967fa_Branch254_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:40:39.865196+00:00
-- url     : https://prove2.me/theorems/e76c51f6-5eac-461f-8204-aac3fb47e774
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

def Polychromatic418967fa.branch_254_segment_000 : allB 123 254 :=
  allB_succ 122 254 (allA_succ_of_accept 121 122 254 (accept_3_2 121 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 122 254 2 60 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 122 254 (Polychromatic418967fa.accept_13_2_5_7_1_1695 119 122 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 122 254 2 59 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 122 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 117 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 122 254 2 58 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 122 254 (accept_3_2 115 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 122 254 2 57 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 122 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 113 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 122 254 2 56 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 122 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 111 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 122 254 2 55 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 122 254 (accept_3_2 109 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 122 254 2 54 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 122 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 107 122 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 254 2 53 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 105 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 254 2 52 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 254 (accept_3_2 103 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 254 2 51 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 254 (Polychromatic418967fa.accept_16_5_10_14_1_5074 101 122 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 254 2 50 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 99 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 254 2 49 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 254 (accept_3_2 97 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 254 2 48 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 254 (Polychromatic418967fa.accept_15_5_2_14_1_1693 95 122 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 254 2 47 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 93 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 254 2 46 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 254 (accept_3_2 91 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 254 2 45 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 254 2 44 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 254 2 43 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 254 (accept_3_2 85 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 254 2 42 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 254 2 41 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 254
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 81 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 122 254 2 40 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 122 254 (accept_3_2 79 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 254 2 39 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 254 2 38 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 122 254 2 37 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 254 (accept_3_2 73 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 254 2 36 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 254 2 35 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 254 2 34 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 254 (accept_3_2 67 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 254 2 33 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 254 (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 122 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 254 2 32 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 254
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 254 2 31 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 254 (accept_3_2 61 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 254 2 30 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 254 (Polychromatic418967fa.accept_23_13_7_1_1_10648 59 122 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 254 2 29 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 254 2 28 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 254 (accept_3_2 55 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 254 2 27 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 254 2 26 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 254 2 25 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 254 (accept_3_2 49 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 254 2 24 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 254 2 23 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 254
  (Polychromatic418967fa.accept_16_13_10_14_1_2871 45 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 122 254 2 22 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 122 254 (accept_3_2 43 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 254 2 21 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 254 2 20 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 254 2 19 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 254 (accept_3_2 37 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 254 2 18 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 254 2 17 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 254 2 16 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 254 (accept_3_2 31 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 254 2 15 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 254 2 14 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 254 2 13 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 254 (accept_3_2 25 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 254 2 12 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 254 (Polychromatic418967fa.accept_16_7_10_14_1_1884 23 122 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 254 2 11 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 254 2 10 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 254 (accept_3_2 19 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 254 2 9 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 122 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 254 2 8 61 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 254 2 7 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 254 (accept_3_2 13 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 254 2 6 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 254 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 122 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 254 2 5 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 254
  (Polychromatic418967fa.accept_19_9_8_7_1_2061 9 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 254 2 4 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 254 (accept_3_2 7 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  254 2 3 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 122 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 254 2 2 61 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 122 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 254 2 1 61 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 254 (accept_3_2 1 122 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 254 (allA_of_3_0 121 121 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 254
  (allA_succ_of_accept 119 120 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 119 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 120 254 2 59 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 120 254
  (Polychromatic418967fa.accept_17_15_1_16_1_8166 117 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 120 254 2 58 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 120 254 (accept_3_2 115 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 120 254 2 57 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 120 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 113 120 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 120 254 2 56 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 120 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 111 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 120 254 2 55 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 120 254 (accept_3_2 109 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 120 254 2 54 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 120 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 107 120 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 120 254 2 53 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 120 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 105 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 120 254 2 52 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 120 254 (accept_3_2 103 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 120 254 2 51 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 120 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 101 120 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 120 254 2 50 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 120 254
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 99 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 120 254 2 49 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 120 254 (accept_3_2 97 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 254 2 48 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 120 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 95 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 120 254 2 47 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 254
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 93 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 120 254 2 46 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 120 254 (accept_3_2 91 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 120 254 2 45 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 120 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 120 254 2 44 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 120 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 120 254 2 43 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 120 254 (accept_3_2 85 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 120 254 2 42 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 120 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 83 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 254 2 41 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 254
  (Polychromatic418967fa.accept_19_5_6_7_1_10003 81 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 120 254 2 40 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 120 254 (accept_3_2 79 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 254 2 39 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 254 2 38 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 120 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 75 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 120 254 2 37 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 120 254 (accept_3_2 73 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 254 2 36 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 254 2 35 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 120 254 2 34 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 120 254 (accept_3_2 67 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 254 2 33 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 254 (Polychromatic418967fa.accept_19_8_6_7_1_7216 65 120 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 254 2 32 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 254
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 120 254 2 31 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 254 (accept_3_2 61 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 254 2 30 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 254 2 29 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 254
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 254 2 28 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 120 254 (accept_3_2 55 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 254 2 27 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 254 2 26 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 254 2 25 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 254 (accept_3_2 49 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 254 2 24 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 254 (Polychromatic418967fa.accept_13_8_3_7_1_2455 47 120 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 254 2 23 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 120 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 120 254 2 22 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 120 254 (accept_3_2 43 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 254 2 21 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 254 2 20 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 254
  (Polychromatic418967fa.accept_17_5_1_16_1_4359 39 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 120 254 2 19 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 120 254 (accept_3_2 37 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 254 2 18 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 254 2 17 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 254 2 16 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 120 254 (accept_3_2 31 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 254 2 15 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 254 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 120 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 254 2 14 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 120 254 2 13 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 120 254 (accept_3_2 25 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 254 2 12 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 254 2 11 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 254
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 254 2 10 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 120 254 (accept_3_2 19 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 254 2 9 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 120 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 254 2 8 60 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 120 254 2 7 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 120 254 (accept_3_2 13 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 120 254 2 6 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 120 254 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 120 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 254 2 5 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 254 2 4 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 254 (accept_3_2 7 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120
  254 2 3 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  120 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 120 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 254 2 2 60 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 120 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 254 2 1 60 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 254 (accept_3_2 1 120 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 254 (allA_succ_of_accept 118 119 254 (accept_3_2 118 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 117 119 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 116
  119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 254 (accept_3_2 115
  119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 254
  (Polychromatic418967fa.accept_21_9_14_2_1_6370 114 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 113 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 254 (accept_3_2 112 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 254
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 110 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 119 254 (accept_3_2 109 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 119 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 108 119 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 119 254 (Polychromatic418967fa.accept_14_9_7_2_1_2483 107 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 254 (accept_3_2 106 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 105 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 119 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 104 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 119 254 (accept_3_2 103 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 119 254 (Polychromatic418967fa.accept_29_15_3_22_1_15509 102 119 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 119 254 (accept_3_2 100 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 119 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 98 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 254 (accept_3_2 97 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 119 254 (Polychromatic418967fa.accept_13_5_2_7_1_2414 96 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 254
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 95 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 119 254 (accept_3_2 94 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 119 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 92 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 119 254 (accept_3_2 91 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 119 254 (Polychromatic418967fa.accept_16_10_7_14_1_2882 90 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 119 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 119 254 (accept_3_2 88 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 119 254 (Polychromatic418967fa.accept_13_8_2_7_1_2452 86 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 254 (accept_3_2 85 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 119 254 (Polychromatic418967fa.accept_16_4_7_14_1_3897 84 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 254
  (Polychromatic418967fa.accept_10_3_9_4_1_960 83 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 119 254 (accept_3_2 82 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 119 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 254 (accept_3_2 79 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 119 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 78 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 119 254 (accept_3_2 76 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 119 254 (Polychromatic418967fa.accept_13_9_2_7_1_1083 74 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 254 (accept_3_2 73 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 254 (Polychromatic418967fa.accept_21_9_14_2_1_6370 72 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 254
  (Polychromatic418967fa.accept_18_17_11_2_1_7782 71 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 119 254 (accept_3_2 70 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 119 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 68 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 254 (accept_3_2 67 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 254
  (Polychromatic418967fa.accept_19_9_5_7_1_5853 66 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 119 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 254 (accept_3_2 64 119 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 254
  (Polychromatic418967fa.accept_21_20_14_2_1_6393 62 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 119 254 (accept_3_2 61 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 119 254 (Polychromatic418967fa.accept_13_8_2_7_1_2452 60 119 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 254 (Polychromatic418967fa.accept_19_2_5_7_1_10021 59 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 254 (accept_3_2 58 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3
  57 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 254 (accept_3_2 55 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 254 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 254 (accept_3_2 52 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 254
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 50 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 119 254 (accept_3_2 49 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 119 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 119 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 254 (Polychromatic418967fa.accept_13_8_2_7_1_2452 47 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 254 (accept_3_2 46 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 254 (accept_3_2 43 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 254 (Polychromatic418967fa.accept_16_10_7_14_1_2882 42 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 254 (accept_3_2 40 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 254
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 254 (accept_3_2 37 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 254 (Polychromatic418967fa.accept_16_4_7_14_1_3897 36 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 254 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 254 (accept_3_2 34 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 254
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 254 (accept_3_2 31 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 254 (Polychromatic418967fa.accept_21_9_14_2_1_6370 30 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 254 (accept_3_2 28 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 254
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 254 (accept_3_2 25 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 254 (Polychromatic418967fa.accept_20_4_19_14_1_5327 24 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 254 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 254 (accept_3_2 22 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 254 (accept_3_2 19 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 254 (accept_3_2 16 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 254
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 119 254 (accept_3_2 13 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 119 254 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 119 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 254 (Polychromatic418967fa.accept_21_11_14_2_1_6371 11 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 254 (accept_3_2 10 119
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3
  9 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 254
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 254 (accept_3_2 7 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 254 (Polychromatic418967fa.accept_19_6_5_7_1_8708 6 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 254 (accept_3_2 4 119 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 254
  (Polychromatic418967fa.accept_19_2_5_7_1_10021 2 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 254 (accept_3_2 1 119 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 254 (allA_of_3_0 118 118 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 254
  (allA_succ_of_accept 116 117 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 116 117 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 254 (accept_3_2 115 117 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 117 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 114 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 254 (accept_3_2 112 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 254 (Polychromatic418967fa.accept_19_15_3_7_1_5875 110 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 254 (accept_3_2 109 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 108 117
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 107 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 254 (accept_3_2 106 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 254 (Polychromatic418967fa.accept_11_6_7_1_1_564 105 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 117 254 (Polychromatic418967fa.accept_22_16_7_12_1_7630 104 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 254 (accept_3_2 103 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 102 117
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 117 254 (accept_3_2 100 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 117 254 (Polychromatic418967fa.accept_21_14_12_2_1_15508 98 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 254 (accept_3_2 97 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 254 (Polychromatic418967fa.accept_17_11_15_16_1_4377 96
  117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 254 (accept_3_2 94 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 93 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 92 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 254 (accept_3_2 91 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 117
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 254 (accept_3_2 88 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 117 254 (Polychromatic418967fa.accept_15_11_12_14_1_2612 86 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 254 (accept_3_2 85 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 84 117
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 254 (accept_3_2 82 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 117 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 254 (accept_3_2 79 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 254 (accept_3_2 76 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 254 (accept_3_2 73 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 254 (accept_3_2 70 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 69 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 254 (Polychromatic418967fa.accept_23_22_2_1_1_13807 68 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 254 (accept_3_2 67 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 117 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 254 (accept_3_2 64 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 62 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 254 (accept_3_2 61 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 117 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 254 (accept_3_2 58 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 254 (Polychromatic418967fa.accept_16_9_5_14_1_6126 57 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 254 (Polychromatic418967fa.accept_15_11_12_14_1_2612 56 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 254 (accept_3_2 55 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 117
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 254 (accept_3_2 52 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 254 (Polychromatic418967fa.accept_11_6_7_1_1_564 50 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 254 (accept_3_2 49 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 254 (Polychromatic418967fa.accept_17_14_15_16_1_1271 48
  117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 254 (accept_3_2 46 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 254 (Polychromatic418967fa.accept_19_6_3_7_1_11437 44 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 254 (accept_3_2 43 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 117
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 254 (accept_3_2 40 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 254 (accept_3_2 37 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 254 (Polychromatic418967fa.accept_25_11_17_4_1_15507 36 117 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 254 (accept_3_2 34 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 254 (accept_3_2 31 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 254 (accept_3_2 28 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 254 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 254 (accept_3_2 25 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 117 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 254 (accept_3_2 22 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 254 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 254 (Polychromatic418967fa.accept_27_20_9_11_1_11705 20 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 254 (accept_3_2 19 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 117 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 254 (accept_3_2 16 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 254 (Polychromatic418967fa.accept_17_14_15_16_1_1271 14 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 254 (accept_3_2 13 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 117
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 254 (accept_3_2 10 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 254 (Polychromatic418967fa.accept_22_8_7_12_1_12369 8 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 254 (accept_3_2 7 117 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 254 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 117 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 254 (accept_3_2 4 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 254 (accept_3_2 1 117 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 254 (allA_succ_of_accept 115 116 254 (accept_3_2 115 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 254 2 57 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 113 116 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 254 2 56 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 111 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 116 254 2 55 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 116 254 (accept_3_2 109 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 254 2 54 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 107 116 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 254 2 53 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 105 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 116 254 2 52 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 116 254 (accept_3_2 103 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 254 2 51 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 101 116 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 254 2 50 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 254
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 99 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 254 2 49 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 254 (accept_3_2 97 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 254 2 48 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 254 2 47 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 93 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 254 2 46 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 254 (accept_3_2 91 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 254 2 45 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 254 2 44 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 87 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 254 2 43 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 254 (accept_3_2 85 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 254 2 42 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 254 2 41 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 254
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 81 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 254 2 40 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 254 (accept_3_2 79 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 254 2 39 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 254 2 38 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 254 2 37 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 254 (accept_3_2 73 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 254 2 36 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 254 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 254 2 35 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 254 2 34 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 254 (accept_3_2 67 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 254 2 33 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 254 2 32 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 254
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 63 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 116 254 2 31 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 116 254 (accept_3_2 61 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 254 2 30 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 254 2 29 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 254 2 28 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 254 (accept_3_2 55 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 254 2 27 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 254 2 26 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 254 2 25 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 254 (accept_3_2 49 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 254 2 24 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 254 2 23 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 254 2 22 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 254 (accept_3_2 43 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 254 2 21 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 254 2 20 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 254 2 19 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 254 (accept_3_2 37 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 254 2 18 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 254 2 17 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 254 2 16 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 254 (accept_3_2 31 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 254 2 15 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 254 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 116 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 254 2 14 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 254 2 13 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 254 (accept_3_2 25 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 254 2 12 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 254 2 11 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 254 2 10 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 254 (accept_3_2 19 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 254 2 9 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 116 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 116 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 254 2 8 58 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 254 2 7 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 116 254 (accept_3_2 13 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 116 254 2 6 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 116 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 116 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 254 2 5 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 254
  (Polychromatic418967fa.accept_14_9_4_2_1_983 9 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 254 2 4 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 254 (accept_3_2 7 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  254 2 3 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 254 2 2 58 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 116 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 116 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 254 2 1 58 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 254 (accept_3_2 1 116 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 254 (allA_of_3_0 115 115 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 254
  (allA_succ_of_accept 113 114 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 113 114 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 254 2 56 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 114 254 (Polychromatic418967fa.accept_9_3_6_2_1_160
  111 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 254 2 55 57 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 254
  (accept_3_2 109 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 114 254 2 54 57 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 114 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 107 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 254 2 53 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 254 (Polychromatic418967fa.accept_12_9_6_2_1_1273 105 114 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 254 2 52 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 254 (accept_3_2 103 114 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 114 254 2 51 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 114 254
  (Polychromatic418967fa.accept_21_17_9_2_1_13903 101 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 114 254 2 50 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 114 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 99 114 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 254 2 49 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 254 (accept_3_2 97 114 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 114 254 2 48 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 114 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 95 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 114 254 2 47 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 114 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 114 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 114 254 2 46 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 254 (accept_3_2 91 114 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 114 254 2 45 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 114 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 89
  114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 254 2 44 57 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 87 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 254 2 43 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 254 (accept_3_2 85 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 254 2 42 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 254 (Polychromatic418967fa.accept_15_8_9_14_1_4577 83 114 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 254 2 41 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 254 2 40 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 254 (accept_3_2 79 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 254 2 39 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 114 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 254 2 38 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 254 2 37 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 254 (accept_3_2 73 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 254 2 36 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 114 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 254 2 35 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 254 2 34 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 254 (accept_3_2 67 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 254 2 33 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 254 (Polychromatic418967fa.accept_15_5_9_14_1_1724 65 114 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 254 2 32 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 254
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 254 2 31 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 254 (accept_3_2 61 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 254 2 30 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 114 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 254 2 29 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 254 2 28 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 254 (accept_3_2 55 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 254 2 27 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 114 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 254 2 26 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 254 2 25 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 254 (accept_3_2 49 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 254 2 24 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 254 (Polychromatic418967fa.accept_13_8_10_7_1_1702 47 114 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 254 2 23 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 254 2 22 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 254 (accept_3_2 43 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 254 2 21 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 114 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 254 2 20 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 254 2 19 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 254 (accept_3_2 37 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 254 2 18 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 114 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 254 2 17 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 254 2 16 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 254 (accept_3_2 31 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 254 2 15 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 254 (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 114 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 254 2 14 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 254 2 13 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 254 (accept_3_2 25 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 254 2 12 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 114 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 254 2 11 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 254 2 10 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 254 (accept_3_2 19 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 254 2 9 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 114 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 254 2 8 57 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 254 2 7 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 254 (accept_3_2 13 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 254 2 6 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 254 (Polychromatic418967fa.accept_17_11_12_16_1_3219 11 114 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 254 2 5 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 254 2 4 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 254 (accept_3_2 7 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  254 2 3 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 114 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 254 2 2 57 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 114 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 254 2 1 57 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 254 (accept_3_2 1 114 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 254 (allA_succ_of_accept 112 113 254 (accept_3_2 112 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 111 113 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 254 (Polychromatic418967fa.accept_13_6_9_7_1_2430 110 113
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 254 (accept_3_2 109 113
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 108 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 107 113 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 254 (accept_3_2 106 113 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 104 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 254 (accept_3_2 103 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 113 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 101 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 254 (accept_3_2 100 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 113 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 98 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 254 (accept_3_2 97 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 254 (accept_3_2 94 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 92 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 254 (accept_3_2 91 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 254 (accept_3_2 88 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 254
  (Polychromatic418967fa.accept_13_8_9_7_1_530 86 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 254 (accept_3_2 85 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 254 (accept_3_2 82 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 254 (accept_3_2 79 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 254 (Polychromatic418967fa.accept_10_7_3_4_1_978 77 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 254 (accept_3_2 76 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 113 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 254
  (Polychromatic418967fa.accept_19_17_18_7_1_11434 74 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 113 254 (accept_3_2 73 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 113 254 (Polychromatic418967fa.accept_19_15_18_7_1_10018 72 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 254 (accept_3_2 70
  113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 113 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 68 113 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 254 (accept_3_2 67 113 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 113 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 254 (Polychromatic418967fa.accept_15_5_8_14_1_432
  65 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 254 (accept_3_2 64
  113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 113 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 113 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 254 (accept_3_2 61 113 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 113 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 254 (accept_3_2 58
  113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 113 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 113 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 254 (accept_3_2 55 113 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 113 254 (Polychromatic418967fa.accept_13_2_9_7_1_164 54 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 254 (accept_3_2 52 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 254 (Polychromatic418967fa.accept_13_11_9_7_1_2484 50 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 254 (accept_3_2 49 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 113 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 254 (accept_3_2 46 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 254 (accept_3_2 43 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 254 (accept_3_2 40 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 254 (accept_3_2 37 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 254 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 254 (accept_3_2 34 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 254 (accept_3_2 31 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 113 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 254
  (Polychromatic418967fa.accept_10_9_3_4_1_985 29 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 254 (accept_3_2 28 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 254 (accept_3_2 25 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 254 (accept_3_2 22 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 254 (accept_3_2 19 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 254 (Polychromatic418967fa.accept_23_18_21_1_1_15506 18 113 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 254 (accept_3_2 16 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 254 (Polychromatic418967fa.accept_17_14_11_16_1_3261 14 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 254 (accept_3_2 13 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 113 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 254 (accept_3_2 10 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 254 (accept_3_2 7 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 113 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 254
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 254 (accept_3_2 4 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 254 (accept_3_2 1 113 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 254 (allA_of_3_0 112 112 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 254
  (allA_succ_of_accept 110 111 254 (Polychromatic418967fa.accept_15_5_6_14_1_1721 110 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 254 (accept_3_2 109 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 108 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 254 (accept_3_2 106 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 104 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 254 (accept_3_2 103 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 102 111
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 101 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 254 (accept_3_2 100 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 99 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 254 (accept_3_2 97 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 254 (accept_3_2 94 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 92 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 254 (accept_3_2 91 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 90 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 254 (accept_3_2 88 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 254 (accept_3_2 85 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 254 (Polychromatic418967fa.accept_15_9_6_14_1_2627 84 111 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 254 (accept_3_2 82 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 254 (accept_3_2 79 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 254 (accept_3_2 76 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 254 (Polychromatic418967fa.accept_10_5_1_4_1_1444 75 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 254 (accept_3_2 73 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 254 (Polychromatic418967fa.accept_21_9_6_2_1_3357 72 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 254 (accept_3_2 70 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 254 (accept_3_2 67 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 254 (accept_3_2 64 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 254 (Polychromatic418967fa.accept_18_9_3_2_1_3814 63 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 254 (accept_3_2 61 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 254 (accept_3_2 58 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 254 (Polychromatic418967fa.accept_21_14_6_2_1_4793 56 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 254 (accept_3_2 55 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 111
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 254 (accept_3_2 52 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 254 (accept_3_2 49 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 254 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 254 (accept_3_2 46 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 254 (accept_3_2 43 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 254 (accept_3_2 40 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 254 (accept_3_2 37 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 254 (accept_3_2 34 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 254 (accept_3_2 31 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 254 (accept_3_2 28 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 254 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 254 (accept_3_2 25 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 254 (accept_3_2 22 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 254 (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 254 (accept_3_2 19 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 111 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 254 (accept_3_2 16 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 254 (accept_3_2 13 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 254 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 254 (accept_3_2 10 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 254 (accept_3_2 7 111 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 254 (accept_3_2 4 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 254 (Polychromatic418967fa.accept_19_2_16_7_1_11424 2 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 254 (accept_3_2 1 111 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 254 (allA_succ_of_accept 109 110 254 (accept_3_2 109 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 254 2 54 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 254 (Polychromatic418967fa.accept_15_2_5_14_1_61 107 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 254 2 53 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 110 254
  (Polychromatic418967fa.accept_13_1_6_7_1_550 105 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 110 254 2 52 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 110 254 (accept_3_2 103 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 110 254 2 51 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 110 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 101 110 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 254 2 50 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 254
  (Polychromatic418967fa.accept_15_9_5_14_1_973 99 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 110 254 2 49 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 110 254 (accept_3_2 97 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 254 2 48 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 95 110 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 254 2 47 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 254
  (Polychromatic418967fa.accept_19_17_15_7_1_10030 93 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 110 254 2 46 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 110 254 (accept_3_2 91 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 254 2 45 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 254 (Polychromatic418967fa.accept_19_13_15_7_1_5843 89 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 254 2 44 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 254 2 43 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 254 (accept_3_2 85 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 254 2 42 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 254 (Polychromatic418967fa.accept_15_8_5_14_1_986 83 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 254 2 41 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 254 2 40 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 254 (accept_3_2 79 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 254 2 39 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 254 (Polychromatic418967fa.accept_13_12_6_7_1_1071 77 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 254 2 38 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 254
  (Polychromatic418967fa.accept_17_7_8_16_1_6966 75 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 254 2 37 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 254 (accept_3_2 73 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 254 2 36 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 254 (Polychromatic418967fa.accept_19_14_15_7_1_7205 71 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 254 2 35 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 254
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 69 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 254 2 34 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 254 (accept_3_2 67 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 254 2 33 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 254 (Polychromatic418967fa.accept_17_14_8_16_1_6863 65 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 254 2 32 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 254
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 63 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 254 2 31 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 254 (accept_3_2 61 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 254 2 30 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 110 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 254 2 29 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 254
  (Polychromatic418967fa.accept_25_7_10_4_1_15505 57 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 110 254 2 28 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 110 254 (accept_3_2 55 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 254 2 27 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 110 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 254 2 26 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 254
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 51 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 254 2 25 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 254 (accept_3_2 49 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 254 2 24 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 254 (Polychromatic418967fa.accept_15_2_5_14_1_61 47 110 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 254 2 23 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 254 2 22 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 254 (accept_3_2 43 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 254 2 21 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 254 (Polychromatic418967fa.accept_17_7_8_16_1_6966 41 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 254 2 20 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 254 2 19 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 254 (accept_3_2 37 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 254 2 18 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 254 (Polychromatic418967fa.accept_13_9_6_7_1_551 35 110 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 254 2 17 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 254
  (Polychromatic418967fa.accept_19_14_15_7_1_7205 33 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 110 254 2 16 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 110 254 (accept_3_2 31 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 254 2 15 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 254 (Polychromatic418967fa.accept_21_8_5_2_1_8004 29 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 254 2 14 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 254
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 254 2 13 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 254 (accept_3_2 25 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 254 2 12 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 254 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 254 2 11 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 254
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 21 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 254 2 10 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 254 (accept_3_2 19 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 254 2 9 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 110 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 254 2 8 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 254
  (Polychromatic418967fa.accept_20_15_10_14_1_11245 15 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 110 254 2 7 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 110 254 (accept_3_2 13 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 254 2 6 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 110 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 254 2 5 55 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 254
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 254 2 4 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 254 (accept_3_2 7 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  254 2 3 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 254 (Polychromatic418967fa.accept_20_5_10_14_1_5317 5 110 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 254 2 2 55 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 110 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 254 2 1 55 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 254 (accept_3_2 1 110 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 254 (allA_of_3_0 109 109 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 254
  (allA_succ_of_accept 107 108 254 (Polychromatic418967fa.accept_13_3_4_7_1_1711 107 108 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 254 2 53 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 254
  (Polychromatic418967fa.accept_20_5_8_14_1_5341 105 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 108 254 2 52 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 108 254 (accept_3_2 103 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 254 2 51 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 254 (Polychromatic418967fa.accept_13_10_4_7_1_2465 101 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 254 2 50 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 108 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 99 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 108 254 2 49 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 108 254 (accept_3_2 97 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 254 2 48 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 254 (Polychromatic418967fa.accept_17_10_6_16_1_6862 95 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 254 2 47 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 108 254
  (Polychromatic418967fa.accept_19_17_13_7_1_5861 93 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 108 254 2 46 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 108 254 (accept_3_2 91 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 254 2 45 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 108 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 254 2 44 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 108 254
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 87 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 108 254 2 43 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 108 254 (accept_3_2 85 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 254 2 42 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 108 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 254 2 41 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 108 254
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 81 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 108 254 2 40 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 108 254 (accept_3_2 79 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 254 2 39 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 254 (Polychromatic418967fa.accept_13_12_4_7_1_2520 77 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 254 2 38 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 108 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 75 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 108 254 2 37 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 108 254 (accept_3_2 73 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 254 2 36 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 108 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 254 2 35 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 69 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 254 2 34 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 254 (accept_3_2 67 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 254 2 33 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 254 (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 254 2 32 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 254
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 63 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 108 254 2 31 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 108 254 (accept_3_2 61 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 254 2 30 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 108 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 254 2 29 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 254 2 28 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 254 (accept_3_2 55 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 254 2 27 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 254 (Polychromatic418967fa.accept_19_15_13_7_1_7246 53 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 254 2 26 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 254
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 51 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 108 254 2 25 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 254 (accept_3_2 49 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 254 2 24 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 108 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 254 2 23 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 254
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 254 2 22 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 254 (accept_3_2 43 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 254 2 21 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 254 2 20 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 254 2 19 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 254 (accept_3_2 37 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 254 2 18 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 254 (Polychromatic418967fa.accept_13_9_4_7_1_1694 35 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 254 2 17 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 108 254 2 16 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 108 254 (accept_3_2 31 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 254 2 15 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 254 2 14 54 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 254 2 13 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 254 (accept_3_2 25 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 254 2 12 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 254 (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 254 2 11 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 254
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 254 2 10 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 108 254 (accept_3_2 19 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 254 2 9 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 108 254 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 254 2 8 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 108 254 2 7 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 108 254 (accept_3_2 13 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 254 2 6 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 108 254 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 254 2 5 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 254 2 4 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 254 (accept_3_2 7 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108
  254 2 3 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  108 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 254 2 2 54 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 108 254 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 108 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 254 2 1 54 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 254 (accept_3_2 1 108 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 254 (allA_succ_of_accept 106 107 254 (accept_3_2 106 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 105 107 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 107
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 254 (accept_3_2 103 107
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 102 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 101 107 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 254 (accept_3_2 100 107 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 254
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 98 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 107 254 (accept_3_2 97 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 107 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 107 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 254 (accept_3_2 94 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 92 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 107 254 (accept_3_2 91 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 107 254 (Polychromatic418967fa.accept_19_14_12_7_1_10027 90 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 254 (accept_3_2 88 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 107 254 (accept_3_2 85 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 107 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 107 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 83 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 254 (accept_3_2 82 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 107 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 80 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 254 (accept_3_2 79 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 254 (accept_3_2 76 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 254
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 74 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 254 (accept_3_2 73 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 254 (Polychromatic418967fa.accept_10_1_7_4_1_968 71 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 254 (accept_3_2 70 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 107 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 254 (accept_3_2 67 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 254 (accept_3_2 64 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 62 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 254 (accept_3_2 61 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 254 (accept_3_2 58 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 254 (accept_3_2 55 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 254 (Polychromatic418967fa.accept_19_16_12_7_1_8712 54 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 254 (accept_3_2 52 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 254 (accept_3_2 49 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 254 (Polychromatic418967fa.accept_13_8_3_7_1_2455 47 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 254 (accept_3_2 46 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 254 (accept_3_2 43 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 254 (accept_3_2 40 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 254
  (Polychromatic418967fa.accept_17_4_5_16_1_3240 38 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 254 (accept_3_2 37 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 254 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 254 (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 254 (accept_3_2 34 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 254 (accept_3_2 31 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 254 (accept_3_2 28 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 254
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 254 (accept_3_2 25 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 254 (accept_3_2 22 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 254 (accept_3_2 19 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 254 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 254 (accept_3_2 16 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 254 (accept_3_2 13 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 254 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 254 (accept_3_2 10 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 254 (accept_3_2 7 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 254 (accept_3_2 4 107 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 254 (accept_3_2 1 107 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 254 (allA_of_3_0 106 106 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 254
  (allA_succ_of_accept 104 105 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 104 105 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 254 (accept_3_2 103 105 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 105 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 254 (accept_3_2 100 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 254 (accept_3_2 97 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 96 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 254 (accept_3_2 94 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 254 (Polychromatic418967fa.accept_17_7_3_16_1_2208 92 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 254 (accept_3_2 91 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 105
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 254 (accept_3_2 88 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 254 (accept_3_2 85 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 254 (accept_3_2 82 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 81 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 254 (accept_3_2 79 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 254 (accept_3_2 76 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 254 (Polychromatic418967fa.accept_19_17_10_7_1_11430 74 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 254 (accept_3_2 73 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 254 (Polychromatic418967fa.accept_17_4_3_16_1_9483 72 105
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 254 (accept_3_2 70 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 254 (Polychromatic418967fa.accept_10_9_5_4_1_966 69 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 254 (accept_3_2 67 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 254 (accept_3_2 64 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 254 (accept_3_2 61 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 254 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 254 (accept_3_2 58 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 254 (accept_3_2 55 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 105
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 254 (accept_3_2 52 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 254 (accept_3_2 49 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 254 (accept_3_2 46 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 254 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 254 (accept_3_2 43 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 254 (accept_3_2 40 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 254 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 254 (accept_3_2 37 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 105
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 254 (accept_3_2 34 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 254 (Polychromatic418967fa.accept_14_5_7_2_1_468 33 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 254 (accept_3_2 31 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 254 (accept_3_2 28 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 254 (accept_3_2 25 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 254 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 105 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 254 (accept_3_2 22 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 254 (Polychromatic418967fa.accept_16_4_9_14_1_3883 20 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 254 (accept_3_2 19 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 254 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 105
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 254 (accept_3_2 16 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 254 (accept_3_2 13 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 254 (accept_3_2 10 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 254 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 254 (accept_3_2 7 105 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 254 (accept_3_2 4 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 254 (Polychromatic418967fa.accept_25_2_5_4_1_15504 2 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 254 (accept_3_2 1 105 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 254 (allA_succ_of_accept 103 104 254 (accept_3_2 103 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 254 2 51 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 254 2 50 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 99 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 254 2 49 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 254 (accept_3_2 97 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 254 2 48 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 95 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 254 2 47 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 93 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 254 2 46 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 254 (accept_3_2 91 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 254 2 45 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 254 2 44 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 87 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 254 2 43 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 254 (accept_3_2 85 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 254 2 42 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 83 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 254 2 41 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 254 2 40 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 254 (accept_3_2 79 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 254 2 39 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 254 2 38 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 254 2 37 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 254 (accept_3_2 73 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 254 2 36 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 254 2 35 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 254 2 34 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 254 (accept_3_2 67 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 254 2 33 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 254 2 32 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 254
  (Polychromatic418967fa.accept_20_3_4_14_1_3918 63 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 254 2 31 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 254 (accept_3_2 61 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 254 2 30 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 254 2 29 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 254 2 28 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 254 (accept_3_2 55 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 254 2 27 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 254 2 26 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 254 2 25 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 254 (accept_3_2 49 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 254 2 24 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 104 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 254 2 23 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 254 2 22 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 254 (accept_3_2 43 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 254 2 21 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 254 2 20 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 254 2 19 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 254 (accept_3_2 37 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 254 2 18 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 254 2 17 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 254 2 16 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 254 (accept_3_2 31 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 254 2 15 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 254 2 14 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 254
  (Polychromatic418967fa.accept_19_8_9_7_1_312 27 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 254 2 13 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 254 (accept_3_2 25 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 254 2 12 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 104 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 254 2 11 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 254 2 10 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 254 (accept_3_2 19 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 254 2 9 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 104 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 254 2 8 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 104 254 2 7 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 104 254 (accept_3_2 13 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 104 254 2 6 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 104 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 254 2 5 52 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 254
  (Polychromatic418967fa.accept_20_9_4_14_1_8344 9 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 254 2 4 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 254 (accept_3_2 7 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  254 2 3 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 104 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 254 2 2 52 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 104 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 104 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 254 2 1 52 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 254 (accept_3_2 1 104 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 254 (allA_of_3_0 103 103 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 254 (allA_succ_of_accept 101
  102 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 101 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 254 2 50 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 99 102 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 254 2 49 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 254 (accept_3_2 97 102 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 254 2 48 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 254 2 47 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 254 (Polychromatic418967fa.accept_12_9_6_2_1_1273 93 102 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 254 2 46 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 254 (accept_3_2 91 102 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 254 2 45 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 102 254 2 44 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 102 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 254 2 43 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 254 (accept_3_2 85 102 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 102 254 2 42 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 102 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 83
  102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 254 2 41 51 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 102 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 102 254 2 40 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 102 254 (accept_3_2 79 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 254 2 39 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 254 2 38 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 254 2 37 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 254 (accept_3_2 73 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 254 2 36 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 254 2 35 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 254 2 34 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 254 (accept_3_2 67 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 254 2 33 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 254 (Polychromatic418967fa.accept_14_9_4_2_1_983 65 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 254 2 32 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 254 2 31 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 254 (accept_3_2 61 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 254 2 30 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 254 2 29 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 254 2 28 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 254 (accept_3_2 55 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 254 2 27 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 254 2 26 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 254 2 25 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 254 (accept_3_2 49 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 254 2 24 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 254 2 23 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 254 2 22 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 254 (accept_3_2 43 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 254 2 21 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 254 2 20 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 254 2 19 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 254 (accept_3_2 37 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 254 2 18 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 254 2 17 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 254 2 16 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 254 (accept_3_2 31 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 254 2 15 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 254 (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 102 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 254 2 14 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 254 2 13 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 254 (accept_3_2 25 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 254 2 12 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 254 2 11 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 254 2 10 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 254 (accept_3_2 19 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 254 2 9 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 102 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 254 2 8 51 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 254 2 7 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 254 (accept_3_2 13 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 254 2 6 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 254 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 102 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 254 2 5 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 254 2 4 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 254 (accept_3_2 7 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  254 2 3 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 254 2 2 51 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 102 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 254 2 1 51 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 254 (accept_3_2 1 102 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 254 (allA_succ_of_accept 100 101 254 (accept_3_2 100 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 99 101 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 254 (Polychromatic418967fa.accept_11_10_2_1_1_1036 98 101
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 254 (accept_3_2 97 101
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 96 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 95 101 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 101 254 (accept_3_2 94 101 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 101 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 92
  101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 254 (accept_3_2 91
  101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 90 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 101 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 101 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 254 (accept_3_2 88 101 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 254
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 86 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 254 (accept_3_2 85 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 254 (Polychromatic418967fa.accept_19_8_6_7_1_7216 84 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 254 (accept_3_2 82 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 254
  (Polychromatic418967fa.accept_11_3_2_1_1_994 80 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 254 (accept_3_2 79 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 254 (Polychromatic418967fa.accept_10_7_1_4_1_1447 77 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 254 (accept_3_2 76 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 101 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 254
  (Polychromatic418967fa.accept_16_10_5_14_1_6173 74 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 101 254 (accept_3_2 73 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 101 254 (Polychromatic418967fa.accept_15_12_11_14_1_3464 72 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 254 (accept_3_2 70
  101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 101 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 101 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 254 (accept_3_2 67 101 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 101 254 (Polychromatic418967fa.accept_20_6_1_14_1_11258 66 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 254
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 65 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 254 (accept_3_2 64 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 254 (accept_3_2 61 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 254 (Polychromatic418967fa.accept_13_8_10_7_1_1702 60 101 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 254 (accept_3_2 58 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 254 (accept_3_2 55 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 101 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 254
  (Polychromatic418967fa.accept_18_17_11_2_1_7782 53 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 101 254 (accept_3_2 52 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 101 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 254 (accept_3_2 49 101 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 254 (Polychromatic418967fa.accept_7_6_3_2_1_461
  48 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 254 (accept_3_2 46 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 254 (accept_3_2 43 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 254 (Polychromatic418967fa.accept_13_3_10_7_1_1061 42 101
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 254 (accept_3_2 40 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 254 (Polychromatic418967fa.accept_13_12_10_7_1_2433 38 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 254 (accept_3_2 37 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 254 (accept_3_2 34 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 254 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 254 (accept_3_2 31 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 254 (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 101
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 254 (accept_3_2 28 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 254 (accept_3_2 25 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 254 (Polychromatic418967fa.accept_19_5_6_7_1_10003 24 101 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 254 (accept_3_2 22 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 254 (accept_3_2 19 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 254 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 101 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 254
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 254 (accept_3_2 16 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 254 (accept_3_2 13 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 254 (accept_3_2 10 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 254 (accept_3_2 7 101 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 254 (accept_3_2 4 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 254 (Polychromatic418967fa.accept_23_2_9_1_1_15503 2 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 254 (accept_3_2 1 101 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 101
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 254 (allA_of_3_0 100 100 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 254 (allA_succ_of_accept 98 99
  254 (Polychromatic418967fa.accept_10_8_9_4_1_961 98 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 254 (accept_3_2 97 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 254 (Polychromatic418967fa.accept_15_6_9_14_1_3457 96 99 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 254 (accept_3_2 94 99 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93
  99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 254
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 92 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 254 (accept_3_2 91 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 89 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 254 (accept_3_2 88 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 254
  (Polychromatic418967fa.accept_20_6_19_14_1_8387 86 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 254 (accept_3_2 85 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 254 (Polychromatic418967fa.accept_20_4_19_14_1_5327 84 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 254 (accept_3_2 82 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 254 (accept_3_2 79 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 78 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 254 (accept_3_2 76 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 254 (Polychromatic418967fa.accept_10_5_9_4_1_1420 75 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 254
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 74 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 254 (accept_3_2 73 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 254 (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 254 (accept_3_2 70 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 254
  (Polychromatic418967fa.accept_10_8_9_4_1_961 68 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 254 (accept_3_2 67 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 254 (accept_3_2 64 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 254 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 254 (accept_3_2 61 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 254 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 254 (accept_3_2 58 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 254
  (Polychromatic418967fa.accept_27_2_18_11_1_11668 56 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 99 254 (accept_3_2 55 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 99 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 99 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 99 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 254 (accept_3_2 52 99 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 254 (Polychromatic418967fa.accept_13_12_8_7_1_2526
  51 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 254
  (Polychromatic418967fa.accept_14_8_1_2_1_965 50 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 254 (accept_3_2 49 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 254 (accept_3_2 46 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 254
  (Polychromatic418967fa.accept_20_4_19_14_1_5327 44 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 254 (accept_3_2 43 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 254 (accept_3_2 40 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 254 (Polychromatic418967fa.accept_18_3_9_2_1_5053 39 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 254 (accept_3_2 37 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 254 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 254 (accept_3_2 34 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 254
  (Polychromatic418967fa.accept_17_15_14_16_1_5625 32 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 99 254 (accept_3_2 31 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 99 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 99 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 254 (accept_3_2 28 99 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 27
  99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 254
  (Polychromatic418967fa.accept_20_6_19_14_1_8387 26 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 254 (accept_3_2 25 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 254 (accept_3_2 22 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 254 (accept_3_2 19 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 254 (accept_3_2 16 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 254 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 254
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 254 (accept_3_2 13 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 254 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 254 (accept_3_2 10 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 254
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 254 (accept_3_2 7 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 254 (accept_3_2 4 99 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 254 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2
  99 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 254 (accept_3_2 1 99 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  254 (allA_succ_of_accept 97 98 254 (accept_3_2 97 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 254 2 48 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 98 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 254 2 47 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 93
  98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 254 2 46 49 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 254 (accept_3_2 91
  98 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 254 2 45 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 89 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 254 2 44 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 87 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 254 2 43 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 254 (accept_3_2 85 98 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 254 2 42 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 254 (Polychromatic418967fa.accept_21_20_14_2_1_6393
  83 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 254 2 41 49 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 254
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 81 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 254 2 40 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 254 (accept_3_2 79 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 254 2 39 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 254 2 38 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 254 2 37 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 254 (accept_3_2 73 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 254 2 36 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 254 (Polychromatic418967fa.accept_17_3_13_16_1_2183 71 98 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 254 2 35 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 254 2 34 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 254 (accept_3_2 67 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 254 2 33 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 254 (Polychromatic418967fa.accept_15_5_8_14_1_432 65 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 254 2 32 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 254
  (Polychromatic418967fa.accept_17_12_13_16_1_3226 63 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 98 254 2 31 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 98 254 (accept_3_2 61 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 254 2 30 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 254 2 29 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 254 2 28 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 254 (accept_3_2 55 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 254 2 27 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 254 2 26 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 254 2 25 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 254 (accept_3_2 49 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 254 2 24 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 254 (Polychromatic418967fa.accept_27_20_17_11_1_15502 47 98 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 254 2 23 49 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 254
  (Polychromatic418967fa.accept_21_3_14_2_1_7978 45 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 254 2 22 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 254 (accept_3_2 43 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 254 2 21 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 254 2 20 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 254 2 19 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 254 (accept_3_2 37 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 254 2 18 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 254 2 17 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 254 2 16 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 254 (accept_3_2 31 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 254 2 15 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 254 2 14 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 254
  (Polychromatic418967fa.accept_21_6_14_2_1_7980 27 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 254 2 13 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 254 (accept_3_2 25 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 254 2 12 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 254 2 11 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 254 2 10 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 98 254 (accept_3_2 19 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 254 2 9 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 254 (Polychromatic418967fa.accept_18_17_8_2_1_2622 17 98 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 254 2 8 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 254 2 7 49 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 254 (accept_3_2 13
  98 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 254 2 6 49 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 254
  (Polychromatic418967fa.accept_21_11_14_2_1_6371 11 98 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 254 2 5 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 98 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 254 2 4 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 254 (accept_3_2 7 98 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 254 2 3 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 254 2 2 49 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 98
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 254 2 1 49 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 254 (accept_3_2 1 98
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  254 (allA_of_3_0 97 97 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 254 (allA_succ_of_accept 95 96 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 95 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 254 2 47 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 254 2 46 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 254 (accept_3_2 91 96 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 254 2 45 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 89
  96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 254 2 44 48 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 254 2 43 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 254 (accept_3_2 85 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 254 2 42 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 96 254 (Polychromatic418967fa.accept_15_8_6_14_1_975 83 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 254 2 41 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 81 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 96 254 2 40 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 96 254 (accept_3_2 79 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 254 2 39 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 96 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96 254 2 38 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 96 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 96 254 2 37 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 96 254 (accept_3_2 73 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 254 2 36 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 96 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 254 2 35 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 254
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 69 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 254 2 34 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 96 254 (accept_3_2 67 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 254 2 33 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 96 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 254 2 32 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 96 254
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 96 254 2 31 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 96 254 (accept_3_2 61 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 254 2 30 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 96 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 254 2 29 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 254 2 28 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 96 254 (accept_3_2 55 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 254 2 27 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 96 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 254 2 26 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 254
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 254 2 25 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 96 254 (accept_3_2 49 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 254 2 24 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 96 254 (Polychromatic418967fa.accept_29_18_9_22_1_15501 47 96 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 254 2 23 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 254 2 22 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 96 254 (accept_3_2 43 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 254 2 21 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 96 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 254 2 20 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 96 254 2 19 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 96 254 (accept_3_2 37 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 254 2 18 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 96 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 254 2 17 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 254
  (Polychromatic418967fa.accept_22_11_8_12_1_1581 33 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 254 2 16 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 96 254 (accept_3_2 31 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 254 2 15 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 96 254 (Polychromatic418967fa.accept_17_12_11_16_1_6903 29 96 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 254 2 14 48 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 254
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 27 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 96 254 2 13 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 96 254 (accept_3_2 25 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 254 2 12 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 96 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 254 2 11 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 254 2 10 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 254 (accept_3_2 19 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 254 2 9 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 254 2 8 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 254 2 7 48 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 254 (accept_3_2 13
  96 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 254 2 6 48 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 96 254 2 5 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 96 254 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 96 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 254 2 4 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 254 (accept_3_2 7 96 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 96 254 2 3 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 96 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 254 2 2 48 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 254 2 1 48 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 254 (accept_3_2 1 96
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 254
  (allA_succ_of_accept 94 95 254 (accept_3_2 94 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 92 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 254 (accept_3_2 91 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 95 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 89 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 254 (accept_3_2 88 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 86 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 254 (accept_3_2 85 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 254 (accept_3_2 82 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 254 (accept_3_2 79 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 254 (accept_3_2 76 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 254 (Polychromatic418967fa.accept_13_9_4_7_1_1694 74 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 254 (accept_3_2 73 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 254 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 254 (accept_3_2 70 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 254 (accept_3_2 67 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 254 (accept_3_2 64 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 254 (accept_3_2 61 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 254
  (Polychromatic418967fa.accept_10_9_5_4_1_966 59 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 254 (accept_3_2 58 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 254 (accept_3_2 55 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 254 (accept_3_2 52 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 254 (Polychromatic418967fa.accept_11_6_7_1_1_564 50 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 254 (accept_3_2 49 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 254 (accept_3_2 46 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 254 (accept_3_2 43 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 254 (accept_3_2 40 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 254 (Polychromatic418967fa.accept_13_12_4_7_1_2520 38 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 254 (accept_3_2 37 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 95 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 254 (accept_3_2 34 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 254 (accept_3_2 31 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 95 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 254 (accept_3_2 28 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 254 (accept_3_2 25 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 254
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 254 (accept_3_2 22 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 254 (accept_3_2 19 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 254 (Polychromatic418967fa.accept_22_18_7_12_1_9213 18 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 254 (accept_3_2 16 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 254 (Polychromatic418967fa.accept_21_14_11_2_1_13897 14 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 254 (accept_3_2 13 95 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 254
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 254 (accept_3_2 10 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 254 (accept_3_2 7 95 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 95 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 254 (accept_3_2 4 95 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 254
  (Polychromatic418967fa.accept_15_2_5_14_1_61 2 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 254 (accept_3_2 1 95 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 254
  (allA_of_3_0 94 94 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 254 (allA_succ_of_accept 92 93 254
  (Polychromatic418967fa.accept_15_2_3_14_1_972 92 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 254 (accept_3_2 91 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 90 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 254 (accept_3_2 88 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 86 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 254 (accept_3_2 85 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 254 (Polychromatic418967fa.accept_18_12_3_2_1_756 84 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 254 (accept_3_2 82 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 254 (Polychromatic418967fa.accept_14_11_9_2_1_6382 81 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 80 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 254 (accept_3_2 79 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 254 (accept_3_2 76 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 254
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 74 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 254 (accept_3_2 73 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 254 (accept_3_2 70 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 254 (accept_3_2 67 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 254 (accept_3_2 64 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 254 (accept_3_2 61 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 254 (accept_3_2 58 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 254 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 254
  (Polychromatic418967fa.accept_15_11_3_14_1_971 56 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 254 (accept_3_2 55 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 254 (accept_3_2 52 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 254 (accept_3_2 49 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 254 (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 254 (accept_3_2 46 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 254 (Polychromatic418967fa.accept_18_9_3_2_1_3814 45 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 254 (accept_3_2 43 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 254 (accept_3_2 40 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 254
  (Polychromatic418967fa.accept_21_17_9_2_1_13903 38 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 254 (accept_3_2 37 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 254 (Polychromatic418967fa.accept_17_2_8_16_1_4403 36 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 254 (accept_3_2 34 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 254 (accept_3_2 31 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 254 (accept_3_2 28 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 254 (accept_3_2 25 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 254 (accept_3_2 22 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 254 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 254
  (Polychromatic418967fa.accept_21_20_9_2_1_15500 20 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 254 (accept_3_2 19 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 254 (accept_3_2 16 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 254 (accept_3_2 13 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 254 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 254 (accept_3_2 10 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 254 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 93 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 254 (accept_3_2 7 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  254 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 254 (accept_3_2 4 93 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 254 (Polychromatic418967fa.accept_15_2_3_14_1_972 2
  93 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 254 (accept_3_2 1 93 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 254
  (allA_succ_of_accept 91 92 254 (accept_3_2 91 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  254 2 45 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 254 2 44 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 92 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 254 2 43 46 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 254 (accept_3_2 85 92 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 254 2 42 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 254 2 41 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 254 (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 254 2 40 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 254 (accept_3_2 79 92 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 254 2 39 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 77
  92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 254 2 38 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 254
  (Polychromatic418967fa.accept_28_19_8_2_1_15499 75 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 254 2 37 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 254 (accept_3_2 73 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 254 2 36 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 92 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 71 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 254 2 35 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 92 254 2 34 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 92 254 (accept_3_2 67 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 92 254 2 33 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 92 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 92 254 2 32 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 92 254
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 92 254 2 31 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 92 254 (accept_3_2 61 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 92 254 2 30 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 92 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 254 2 29 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 254 2 28 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 92 254 (accept_3_2 55 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 92 254 2 27 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 92 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 92 254 2 26 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 254
  (Polychromatic418967fa.accept_26_25_14_20_1_15498 51 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 92 254 2 25 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 92 254 (accept_3_2 49 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 92 254 2 24 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 92 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 92 254 2 23 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 92 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 92 254 2 22 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 92 254 (accept_3_2 43 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 92 254 2 21 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 92 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 254 2 20 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 254
  (Polychromatic418967fa.accept_25_14_17_4_1_15497 39 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 92 254 2 19 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 92 254 (accept_3_2 37 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 254 2 18 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 92 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 254 2 17 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 254
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 33 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 254 2 16 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 92 254 (accept_3_2 31 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 92 254 2 15 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 92 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 254 2 14 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 92 254 2 13 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 92 254 (accept_3_2 25 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 92 254 2 12 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 92 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 254 2 11 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 254
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 254 2 10 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 92 254 (accept_3_2 19 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 92 254 2 9 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 92 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 254 2 8 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 254 (Polychromatic418967fa.accept_14_1_8_2_1_1675
  15 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 254 2 7 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 254 (accept_3_2 13
  92 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 254 2 6 46 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 254
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 92 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 92 254 2 5 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 92 254 (Polychromatic418967fa.accept_19_9_16_7_1_1056 9 92 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 254 2 4 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 254 (accept_3_2 7 92 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 92 254 2 3 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 92 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 92 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 254 2 2 46 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 92
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 254 2 1 46 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 254 (accept_3_2 1 92
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 254
  (allA_of_3_0 91 91 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 254 (allA_succ_of_accept 89 90 254
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 89 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 254 2 44 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 90 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 254 2 43 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 254 (accept_3_2 85 90 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 254 2 42 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 254 (Polychromatic418967fa.accept_13_5_12_7_1_1080
  83 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 254 2 41 45 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 254 2 40 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 254 (accept_3_2 79 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 254 2 39 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 254 (Polychromatic418967fa.accept_16_13_10_14_1_2871 77 90 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 254 2 38 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 254 2 37 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 90 254 (accept_3_2 73 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 254 2 36 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 254 2 35 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 254
  (Polychromatic418967fa.accept_11_3_2_1_1_994 69 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 254 2 34 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 90 254 (accept_3_2 67 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 254 2 33 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 254 (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 254 2 32 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 254 2 31 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 254 (accept_3_2 61 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 254 2 30 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 254 2 29 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 254 2 28 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 90 254 (accept_3_2 55 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 254 2 27 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 254 2 26 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 254 2 25 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 90 254 (accept_3_2 49 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 254 2 24 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 254 2 23 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 254 2 22 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 90 254 (accept_3_2 43 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 254 2 21 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 254 (Polychromatic418967fa.accept_19_3_14_7_1_7204 41 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 254 2 20 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 254 2 19 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 90 254 (accept_3_2 37 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 254 2 18 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 254 (Polychromatic418967fa.accept_17_1_5_16_1_5589 35 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 254 2 17 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 254 2 16 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 254 (accept_3_2 31 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 254 2 15 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 254 2 14 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 254 2 13 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 90 254 (accept_3_2 25 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 254 2 12 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 254 (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 90 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 254 2 11 45 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 254
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 254 2 10 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 90 254 (accept_3_2 19 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 254 2 9 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 90 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 254 2 8 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 254 2 7 45 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 254 (accept_3_2 13
  90 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 254 2 6 45 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 254 2 5 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 254 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 90 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 254 2 4 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 254 (accept_3_2 7 90 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 90 254 2 3 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 90 254 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 90 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 254 2 2 45 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 254 2 1 45 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 254 (accept_3_2 1 90
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 254
  (allA_succ_of_accept 88 89 254 (accept_3_2 88 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 86 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 254 (accept_3_2 85 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 254 (accept_3_2 82 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 254 (accept_3_2 79 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 77 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 254 (accept_3_2 76 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 254 (accept_3_2 73 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 254 (Polychromatic418967fa.accept_19_15_13_7_1_7246 72 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 254 (accept_3_2 70 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 254 (accept_3_2 67 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 254
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 65 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 254 (accept_3_2 64 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 254 (Polychromatic418967fa.accept_18_8_17_2_1_1557 62 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 254 (accept_3_2 61 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 89 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 254 (accept_3_2 58 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 254 (accept_3_2 55 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 254 (Polychromatic418967fa.accept_17_3_4_16_1_3208 54 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 254 (accept_3_2 52 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 254 (accept_3_2 49 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 254 (accept_3_2 46 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 254 (accept_3_2 43 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 254 (accept_3_2 40 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 254 (accept_3_2 37 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 254 (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 254 (accept_3_2 34 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 254 (accept_3_2 31 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 254
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 254 (accept_3_2 28 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 254 (Polychromatic418967fa.accept_18_8_17_2_1_1557 26 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 254 (accept_3_2 25 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 254 (accept_3_2 22 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 254 (accept_3_2 19 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 254 (accept_3_2 16 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 254 (accept_3_2 13 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 254 (accept_3_2 10 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 254 (accept_3_2 7 89 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 89 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 254 (accept_3_2 4 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 254 (Polychromatic418967fa.accept_19_2_13_7_1_7211 2 89 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 254 (accept_3_2 1 89 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 254 (allA_of_3_0 88 88 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 254
  (allA_succ_of_accept 86 87 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 87 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 254 (accept_3_2 85 87 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 254 (accept_3_2 82 87
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3
  81 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 87 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 80 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 87 254 (accept_3_2 79 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  87 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 254 (accept_3_2 76 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 254
  (Polychromatic418967fa.accept_16_10_7_14_1_2882 74 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 254 (accept_3_2 73 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 254 (accept_3_2 70 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 254 (accept_3_2 67 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 254 (accept_3_2 64 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 254 (accept_3_2 61 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 254 (Polychromatic418967fa.accept_13_8_9_7_1_530 60 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 254 (accept_3_2 58 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 254
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 56 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 254 (accept_3_2 55 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 254 (accept_3_2 52 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 254 (Polychromatic418967fa.accept_10_1_7_4_1_968 51 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 254 (accept_3_2 49 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 254 (accept_3_2 46 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 254 (accept_3_2 43 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 254 (accept_3_2 40 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 254
  (Polychromatic418967fa.accept_21_17_3_2_1_2111 38 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 254 (accept_3_2 37 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 254 (accept_3_2 34 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 254 (accept_3_2 31 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 254 (accept_3_2 28 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 254 (accept_3_2 25 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 254 (accept_3_2 22 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 254 (accept_3_2 19 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 254 (accept_3_2 16 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 254 (accept_3_2 13 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 254 (accept_3_2 10 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 254 (accept_3_2 7 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 254 (accept_3_2 4 87 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  87 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 254 (accept_3_2 1 87 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 254
  (allA_succ_of_accept 85 86 254 (accept_3_2 85 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  254 2 42 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 254 (Polychromatic418967fa.accept_17_15_1_16_1_8166 83 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 254 2 41 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 254 (Polychromatic418967fa.accept_13_3_8_7_1_4135 81 86 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 254 2 40 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 254 (accept_3_2 79 86 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 254 2 39 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 254
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 77 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 254 2 38 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 86 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 254 2 37 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 254 (accept_3_2 73 86 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 254 2 36 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 71
  86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 254 2 35 43 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 254 2 34 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 254 (accept_3_2 67 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 254 2 33 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 86 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 254 2 32 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 254
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 254 2 31 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 254 (accept_3_2 61 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 254 2 30 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 254 (Polychromatic418967fa.accept_20_19_6_14_1_3906 59 86 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 254 2 29 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 254 2 28 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 86 254 (accept_3_2 55 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 254 2 27 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 86 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 254 2 26 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 254 2 25 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 254 (accept_3_2 49 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 254 2 24 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 254 (Polychromatic418967fa.accept_18_11_14_2_1_5058 47 86 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 254 2 23 43 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 254 2 22 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 254 (accept_3_2 43 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 254 2 21 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 254 (Polychromatic418967fa.accept_13_2_8_7_1_2424 41 86 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 254 2 20 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 254 2 19 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 86 254 (accept_3_2 37 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 254 2 18 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 254 2 17 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 254 2 16 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 254 (accept_3_2 31 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 254 2 15 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 254 (Polychromatic418967fa.accept_13_3_8_7_1_4135 29 86 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 254 2 14 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 254
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 254 2 13 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 254 (accept_3_2 25 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 254 2 12 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 254 (Polychromatic418967fa.accept_13_10_8_7_1_1074 23 86 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 254 2 11 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 254 2 10 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 254 (accept_3_2 19 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 254 2 9 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 86 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 254 2 8 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 254 2 7 43 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 254 (accept_3_2 13
  86 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 254 2 6 43 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 254
  (Polychromatic418967fa.accept_18_11_14_2_1_5058 11 86 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 254 2 5 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 254 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 86 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 254 2 4 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 254 (accept_3_2 7 86 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 254 2 3 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 86 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 254 2 2 43 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 86
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 254 2 1 43 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 254 (accept_3_2 1 86
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 254
  (allA_of_3_0 85 85 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 254 (allA_succ_of_accept 83 84 254
  (Polychromatic418967fa.accept_11_6_7_1_1_564 83 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 254 2 41 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 254 (Polychromatic418967fa.accept_15_6_9_14_1_3457 81 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 254 2 40 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 254 (accept_3_2 79 84 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 254 2 39 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 77
  84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 254 2 38 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 254
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 75 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 254 2 37 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 254 (accept_3_2 73 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 254 2 36 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 84 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 254 2 35 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 84 254 2 34 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 84 254 (accept_3_2 67 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 254 2 33 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 84 254 (Polychromatic418967fa.accept_15_5_9_14_1_1724 65 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 254 2 32 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 84 254
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 63 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 84 254 2 31 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 84 254 (accept_3_2 61 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 84 254 2 30 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 84 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 254 2 29 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 254
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 254 2 28 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 84 254 (accept_3_2 55 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 254 2 27 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 84 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 254 2 26 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 254 2 25 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 84 254 (accept_3_2 49 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 254 2 24 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 84 254 (Polychromatic418967fa.accept_16_15_4_14_1_6123 47 84 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 254 2 23 42 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 254
  (Polychromatic418967fa.accept_23_22_15_1_1_13838 45 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 84 254 2 22 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 84 254 (accept_3_2 43 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 254 2 21 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 84 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 254 2 20 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 254
  (Polychromatic418967fa.accept_11_6_7_1_1_564 39 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 254 2 19 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 84 254 (accept_3_2 37 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 254 2 18 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 84 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 254 2 17 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 254 2 16 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 84 254 (accept_3_2 31 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 254 2 15 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 84 254 (Polychromatic418967fa.accept_20_9_4_14_1_8344 29 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 254 2 14 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 254
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 84 254 2 13 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 84 254 (accept_3_2 25 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 254 2 12 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 84 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 254 2 11 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 254
  (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 254 2 10 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 84 254 (accept_3_2 19 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 254 2 9 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 254 2 8 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 254 2 7 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 254 (accept_3_2 13
  84 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 254 2 6 42 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 254
  (Polychromatic418967fa.accept_19_11_8_7_1_11423 11 84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 84 254 2 5 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 84 254 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 84 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 254 2 4 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 254 (accept_3_2 7 84 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 84 254 2 3 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 84 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 254 2 2 42 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 254 (Polychromatic418967fa.accept_18_3_12_2_1_2639 3
  84 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 254 2 1 42 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 254 (accept_3_2 1 84
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 254
  (allA_succ_of_accept 82 83 254 (accept_3_2 82 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 254 (accept_3_2 79 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 254 (accept_3_2 76 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 254 (accept_3_2 73 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 254 (Polychromatic418967fa.accept_17_4_15_16_1_3231 72 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 254 (accept_3_2 70 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 254 (accept_3_2 67 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 83 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 254 (accept_3_2 64 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 254 (Polychromatic418967fa.accept_11_7_6_1_1_2182 62 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 254 (accept_3_2 61 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 254 (accept_3_2 58 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 254 (accept_3_2 55 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 254 (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 83 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 254 (accept_3_2 52 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 254 (accept_3_2 49 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 254 (Polychromatic418967fa.accept_17_14_15_16_1_1271 48 83 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 254
  (Polychromatic418967fa.accept_10_7_3_4_1_978 47 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 254 (accept_3_2 46 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 254 (accept_3_2 43 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 254 (Polychromatic418967fa.accept_22_20_17_12_1_7595 42 83
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 254 (accept_3_2 40 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 254 (accept_3_2 37 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 254
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 254 (accept_3_2 34 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 254 (accept_3_2 31 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 254 (Polychromatic418967fa.accept_21_9_20_2_1_8000 30 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 254 (accept_3_2 28 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 254 (Polychromatic418967fa.accept_21_5_20_2_1_7948 26 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 254 (accept_3_2 25 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 254
  (Polychromatic418967fa.accept_24_23_11_14_1_15496 23 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 83 254 (accept_3_2 22 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 83 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 83
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 254 (accept_3_2 19 83 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 18
  83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 254 (accept_3_2 16 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 254 (Polychromatic418967fa.accept_17_14_15_16_1_1271 14 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 254 (accept_3_2 13 83 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 254 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 83
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 254 (accept_3_2 10 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 254 (accept_3_2 7 83 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 254 (Polychromatic418967fa.accept_15_6_8_14_1_4575 6 83 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 254 (accept_3_2 4 83 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 254
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 254 (accept_3_2 1 83 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 254 (allA_of_3_0
  82 82 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 254 (allA_succ_of_accept 80 81 254
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 80 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 81 254 (accept_3_2 79 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  81 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 78 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 81 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 254 (accept_3_2 76 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 254
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 74 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 254 (accept_3_2 73 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 254 (Polychromatic418967fa.accept_22_6_15_12_1_15495 72 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 254 (accept_3_2 70 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 254 (accept_3_2 67 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 254 (accept_3_2 64 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 81 254 (accept_3_2 61 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  81 254 (Polychromatic418967fa.accept_13_8_3_7_1_2455 60 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 254 (accept_3_2 58 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 254 (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 254
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 56 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 254 (accept_3_2 55 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 254 (accept_3_2 52 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 254
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 50 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 254 (accept_3_2 49 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 254 (accept_3_2 46 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 254 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 254
  (Polychromatic418967fa.accept_19_6_5_7_1_8708 44 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 254 (accept_3_2 43 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 254 (accept_3_2 40 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 254
  (Polychromatic418967fa.accept_15_8_6_14_1_975 38 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 254 (accept_3_2 37 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 254 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 254 (accept_3_2 34 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 254
  (Polychromatic418967fa.accept_19_13_5_7_1_12705 32 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 254 (accept_3_2 31 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 254 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 254 (accept_3_2 28 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 254 (accept_3_2 25 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 254 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 254 (accept_3_2 22 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 254 (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 254 (accept_3_2 19 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 254 (accept_3_2 16 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 254
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 254 (accept_3_2 13 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 254 (accept_3_2 10 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 254 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 81 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 254
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 254 (accept_3_2 7 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 254 (accept_3_2 4 81 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 254 (Polychromatic418967fa.accept_19_2_5_7_1_10021
  2 81 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 254 (accept_3_2 1 81
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 254
  (allA_succ_of_accept 79 80 254 (accept_3_2 79 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  254 2 39 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  77 80 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 254 2 38 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 80 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 254 2 37 40 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 254 (accept_3_2 73 80 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 254 2 36 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 254 2 35 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 80 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 80 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 254 2 34 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 254 (accept_3_2 67 80 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 254 2 33 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 65
  80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 254 2 32 40 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 254
  (Polychromatic418967fa.accept_23_17_11_1_1_15494 63 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 80 254 2 31 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 80 254 (accept_3_2 61 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 80 254 2 30 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 80 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 254 2 29 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 254 2 28 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 80 254 (accept_3_2 55 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 80 254 2 27 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 80 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 80 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 80 254 2 26 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 80 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 80 254 2 25 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 80 254 (accept_3_2 49 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 80 254 2 24 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 80 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 80 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 254 2 23 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 254
  (Polychromatic418967fa.accept_17_11_12_16_1_3219 45 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 80 254 2 22 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 80 254 (accept_3_2 43 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 80 254 2 21 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 80 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 80 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 80 254 2 20 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 80 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 80 254 2 19 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 80 254 (accept_3_2 37 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 80 254 2 18 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 80 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 80 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 254 2 17 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 254 2 16 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 80 254 (accept_3_2 31 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 80 254 2 15 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 80 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 254 2 14 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 254 2 13 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 80 254 (accept_3_2 25 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 80 254 2 12 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 80 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 80 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 254 2 11 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 254 2 10 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 80 254 (accept_3_2 19 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 80 254 2 9 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 80 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 80 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 254 2 8 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 254 2 7 40 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 254 (accept_3_2 13
  80 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 254 2 6 40 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 254
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 80 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 254 2 5 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 254 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 80 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 254 2 4 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 254 (accept_3_2 7 80 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 80 254 2 3 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 80 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 254 2 2 40 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 80
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 254 2 1 40 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 254 (accept_3_2 1 80
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 254 (allA_of_3_0 79
  79 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 254 (allA_succ_of_accept 77 78 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 78 254 2 38 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 78 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 78 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 254 2 37 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 254 (accept_3_2 73 78 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 254 2 36 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 71
  78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 254 2 35 39 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 254 2 34 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 78 254 (accept_3_2 67 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 78 254 2 33 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 78 254 (Polychromatic418967fa.accept_24_17_6_14_1_11994 65 78 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 254 2 32 39 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 254 2 31 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 254 (accept_3_2 61 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 254 2 30 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 78 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 254 2 29 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 254 2 28 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 254 (accept_3_2 55 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 254 2 27 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 78 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 254 2 26 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 254 2 25 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 254 (accept_3_2 49 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 254 2 24 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 254 (Polychromatic418967fa.accept_15_2_3_14_1_972 47 78 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 254 2 23 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 254 2 22 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 254 (accept_3_2 43 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 254 2 21 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 78 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 254 2 20 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 254 2 19 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 78 254 (accept_3_2 37 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 254 2 18 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 254 2 17 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 254 2 16 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 78 254 (accept_3_2 31 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 254 2 15 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 78 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 254 2 14 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 254 2 13 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 254 (accept_3_2 25 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 254 2 12 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 78 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 254 2 11 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 254 2 10 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 254 (accept_3_2 19 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 254 2 9 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 78 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 254 2 8 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 15
  78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 254 2 7 39 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 254 (accept_3_2 13
  78 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 254 2 6 39 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 254
  (Polychromatic418967fa.accept_15_11_3_14_1_971 11 78 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 254 2 5 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 78 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 254 2 4 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 254 (accept_3_2 7 78 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 254 2 3 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 78 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 254 2 2 39 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 78
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 254 2 1 39 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 254 (accept_3_2 1 78
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 254
  (allA_succ_of_accept 76 77 254 (accept_3_2 76 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 254 (Polychromatic418967fa.accept_16_10_13_14_1_5042 74 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 254 (accept_3_2 73 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 77 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 254 (accept_3_2 70 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 254 (accept_3_2 67 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 254
  (Polychromatic418967fa.accept_14_9_7_2_1_2483 65 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 254 (accept_3_2 64 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 254 (accept_3_2 61 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 254 (accept_3_2 58 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 254 (accept_3_2 55 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 254 (Polychromatic418967fa.accept_14_12_7_2_1_1663 54 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 254 (accept_3_2 52 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 254 (Polychromatic418967fa.accept_13_11_12_7_1_2443 50 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 254 (accept_3_2 49 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 254 (accept_3_2 46 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 254 (accept_3_2 43 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 254
  (Polychromatic418967fa.accept_10_1_7_4_1_968 41 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 254 (accept_3_2 40 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 254 (Polychromatic418967fa.accept_21_17_14_2_1_4762 38 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 254 (accept_3_2 37 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 254 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 77
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 254 (accept_3_2 34 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 254 (accept_3_2 31 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 254
  (Polychromatic418967fa.accept_19_10_1_7_1_10040 29 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 254 (accept_3_2 28 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 254 (accept_3_2 25 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 254 (accept_3_2 22 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 254 (accept_3_2 19 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 254 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 254 (accept_3_2 16 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 254 (Polychromatic418967fa.accept_22_14_11_12_1_7644 14 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 254 (accept_3_2 13 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 254 (accept_3_2 10 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 254 (accept_3_2 7 77 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 254
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 254 (accept_3_2 4 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 77 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 254 (accept_3_2 1 77 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 254 (allA_of_3_0 76 76 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 254 (allA_succ_of_accept 74 75
  254 (Polychromatic418967fa.accept_7_4_5_2_1_243 74 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 254 (accept_3_2 73 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 254 (Polychromatic418967fa.accept_19_15_18_7_1_10018 72 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 254 (accept_3_2 70 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 254 (accept_3_2 67 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 254 (accept_3_2 64 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 254 (Polychromatic418967fa.accept_14_7_5_2_1_2473 63 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 254 (accept_3_2 61 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 254 (accept_3_2 58 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 254
  (Polychromatic418967fa.accept_10_6_5_4_1_571 56 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 254 (accept_3_2 55 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 254 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 254 (accept_3_2 52 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 254 (accept_3_2 49 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 254 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 254 (accept_3_2 46 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 254 (accept_3_2 43 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 254 (accept_3_2 40 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 254 (accept_3_2 37 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 254 (accept_3_2 34 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 254 (accept_3_2 31 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 254 (accept_3_2 28 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 254 (Polychromatic418967fa.accept_17_10_7_16_1_6841 27 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 254 (accept_3_2 25 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 254 (accept_3_2 22 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 254
  (Polychromatic418967fa.accept_17_3_7_16_1_3251 20 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 254 (accept_3_2 19 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 254 (accept_3_2 16 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 254 (accept_3_2 13 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 254 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 254 (accept_3_2 10 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 254 (accept_3_2 7 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  254 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 254 (accept_3_2 4 75 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 254 (Polychromatic418967fa.accept_23_2_6_1_1_15485
  2 75 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 254 (accept_3_2 1 75
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 254 (allA_succ_of_accept
  73 74 254 (accept_3_2 73 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 254 2 36 37 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 254
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 71 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 254 2 35 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 74 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 254 2 34 37 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 254 (accept_3_2 67 74 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 254 2 33 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 254 (Polychromatic418967fa.accept_14_9_4_2_1_983 65
  74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 254 2 32 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 254
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 254 2 31 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 74 254 (accept_3_2 61 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 254 2 30 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 254 (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 74 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 254 2 29 37 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 254
  (Polychromatic418967fa.accept_25_7_24_4_1_15493 57 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 254 2 28 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 254 (accept_3_2 55 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 254 2 27 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 254 (Polychromatic418967fa.accept_16_5_10_14_1_5074 53 74 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 254 2 26 37 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 254
  (Polychromatic418967fa.accept_14_9_4_2_1_983 51 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 254 2 25 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 254 (accept_3_2 49 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 254 2 24 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 74 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 254 2 23 37 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 254
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 254 2 22 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 74 254 (accept_3_2 43 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 254 2 21 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 74 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 254 2 20 37 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 254
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 39 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 254 2 19 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 254 (accept_3_2 37 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 254 2 18 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 254 (Polychromatic418967fa.accept_19_16_17_7_1_5845 35 74 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 254 2 17 37 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 254 2 16 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 254 (accept_3_2 31 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 254 2 15 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 254 (Polychromatic418967fa.accept_13_3_9_7_1_1730 29 74 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 254 2 14 37 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 254 2 13 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 254 (accept_3_2 25 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 254 2 12 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 254 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 74 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 254 2 11 37 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 254
  (Polychromatic418967fa.accept_13_8_9_7_1_530 21 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 254 2 10 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 254 (accept_3_2 19 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 254 2 9 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 254 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 74 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 254 2 8 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 254 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  15 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 254 2 7 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 254 (accept_3_2 13
  74 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 254 2 6 37 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 254
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 254 2 5 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 254 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 74 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 254 2 4 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 254 (accept_3_2 7 74 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 254 2 3 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 74 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 254 2 2 37 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 254 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3
  74 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 254 2 1 37 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 254 (accept_3_2 1 74
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 254 (allA_of_3_0 73 73 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 254 (allA_succ_of_accept 71 72 254
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 254 2 35 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 72 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 69 72 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 254 2 34 36 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 254 (accept_3_2 67 72 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 254 2 33 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 254 (Polychromatic418967fa.accept_19_8_15_7_1_323
  65 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 254 2 32 36 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 254
  (Polychromatic418967fa.accept_22_19_6_12_1_12330 63 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 72 254 2 31 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 72 254 (accept_3_2 61 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 254 2 30 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 72 254 (Polychromatic418967fa.accept_21_17_9_2_1_13903 59 72 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 254 2 29 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 72 254 2 28 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 72 254 (accept_3_2 55 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 254 2 27 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 72 254 (Polychromatic418967fa.accept_21_11_9_2_1_6354 53 72 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 254 2 26 36 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 254
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 254 2 25 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 72 254 (accept_3_2 49 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 254 2 24 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 72 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 72 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 254 2 23 36 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 254
  (Polychromatic418967fa.accept_21_3_9_2_1_6368 45 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 254 2 22 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 72 254 (accept_3_2 43 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 254 2 21 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 72 254 (Polychromatic418967fa.accept_15_11_12_14_1_2612 41 72 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 254 2 20 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 254
  (Polychromatic418967fa.accept_15_9_12_14_1_963 39 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 72 254 2 19 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 72 254 (accept_3_2 37 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 254 2 18 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 72 254 (Polychromatic418967fa.accept_21_14_9_2_1_8005 35 72 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 254 2 17 36 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 254
  (Polychromatic418967fa.accept_19_14_15_7_1_7205 33 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 254 2 16 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 72 254 (accept_3_2 31 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 254 2 15 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 72 254 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 72 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 254 2 14 36 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 72 254 2 13 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 72 254 (accept_3_2 25 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 254 2 12 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 72 254 (Polychromatic418967fa.accept_28_23_16_2_1_15492 23 72 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 254 2 11 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 254
  (Polychromatic418967fa.accept_23_21_3_1_1_7150 21 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 254 2 10 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 254 (accept_3_2 19 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 254 2 9 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 72 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 254 2 8 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 254 (Polychromatic418967fa.accept_17_15_4_16_1_6890
  15 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 254 2 7 36 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 254 (accept_3_2 13
  72 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 254 2 6 36 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 254
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 72 254 2 5 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 72 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 72 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 254 2 4 36 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 254 (accept_3_2 7 72 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 254 2 3 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 254 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 72 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 254 2 2 36 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 254
  (Polychromatic418967fa.accept_17_3_4_16_1_3208 3 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 72 254 2 1 36 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 254 (accept_3_2 1 72 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 254 (allA_succ_of_accept 70
  71 254 (accept_3_2 70 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 71 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 254 (accept_3_2 67 71 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 254 (accept_3_2 64 71
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 254 (Polychromatic418967fa.accept_6_3_5_2_1_12
  63 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 71 254 (accept_3_2 61 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  71 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 71 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 254 (accept_3_2 58 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 254 (accept_3_2 55 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 254 (Polychromatic418967fa.accept_23_8_2_1_1_15491 54 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 254 (accept_3_2 52 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 254 (accept_3_2 49 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 254 (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 254 (accept_3_2 46 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 254 (accept_3_2 43 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 254 (accept_3_2 40 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 254 (accept_3_2 37 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 254 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 254 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 254 (accept_3_2 34 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 254 (accept_3_2 31 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 254 (accept_3_2 28 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 254
  (Polychromatic418967fa.accept_16_10_7_14_1_2882 26 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 254 (accept_3_2 25 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 254 (accept_3_2 22 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 254 (accept_3_2 19 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 254 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 254 (accept_3_2 16 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 254 (accept_3_2 13 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 254 (Polychromatic418967fa.accept_18_11_17_2_1_6349 11 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 254 (accept_3_2 10 71 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 254 (accept_3_2 7 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 254 (accept_3_2 4 71 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 254 (Polychromatic418967fa.accept_19_2_14_7_1_12783
  2 71 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 254 (accept_3_2 1 71
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 254 (allA_of_3_0 70 70 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 254 (allA_succ_of_accept 68 69 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 254 (accept_3_2 67 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 254 (accept_3_2 64 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 254 (accept_3_2 61 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 254 (accept_3_2 58 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 254
  (Polychromatic418967fa.accept_17_5_1_16_1_4359 56 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 254 (accept_3_2 55 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 254 (accept_3_2 52 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 254 (accept_3_2 49 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 254 (accept_3_2 46 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 254 (accept_3_2 43 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 254 (accept_3_2 40 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 254 (accept_3_2 37 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 254 (accept_3_2 34 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 254 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 254 (accept_3_2 31 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 254 (accept_3_2 28 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 254 (accept_3_2 25 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 254 (accept_3_2 22 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 254
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 254 (accept_3_2 19 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 254 (accept_3_2 16 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 254 (accept_3_2 13 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 254 (accept_3_2 10 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 254 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 69 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 254 (accept_3_2 7 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  254 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 254 (accept_3_2 4 69 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 2
  69 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 254 (accept_3_2 1 69 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 254 (allA_succ_of_accept 67 68
  254 (accept_3_2 67 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 254 2 33 34 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 254
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 254 2 32 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 68 254 (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 68 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 254 2 31 34 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 254 (accept_3_2 61 68 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 254 2 30 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 59
  68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 254 2 29 34 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 254 2 28 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 68 254 (accept_3_2 55 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 68 254 2 27 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 68 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 68 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 254 2 26 34 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 254 2 25 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 68 254 (accept_3_2 49 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 68 254 2 24 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 68 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 68 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 68 254 2 23 34 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 68 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 68 254 2 22 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 68 254 (accept_3_2 43 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 68 254 2 21 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 68 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 68 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 254 2 20 34 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 254 2 19 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 68 254 (accept_3_2 37 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 68 254 2 18 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 68 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 254 2 17 34 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 254 2 16 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 68 254 (accept_3_2 31 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 68 254 2 15 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 68 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 68 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 254 2 14 34 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 254
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 254 2 13 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 68 254 (accept_3_2 25 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 68 254 2 12 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 68 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 68 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 254 2 11 34 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 254 2 10 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 68 254 (accept_3_2 19 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 68 254 2 9 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 68 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 254 2 8 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 254 2 7 34 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 254 (accept_3_2 13
  68 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 254 2 6 34 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 68 254 2 5 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 68 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 68 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 254 2 4 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 254 (accept_3_2 7 68 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 68 254 2 3 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 68 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 68 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 254 2 2 34 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 254 2 1 34 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 254 (accept_3_2 1 68
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 254 (allA_of_3_0 67 67 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 254 (allA_succ_of_accept 65 66 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 65 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 254 2 32 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 66 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 254 2 31 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 254 (accept_3_2 61 66 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 254 2 30 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 59
  66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 254 2 29 33 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 254 2 28 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 254 (accept_3_2 55 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 254 2 27 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 66 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 254 2 26 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 254 2 25 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 254 (accept_3_2 49 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 254 2 24 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 66 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 254 2 23 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 254 2 22 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 254 (accept_3_2 43 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 254 2 21 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 66 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 254 2 20 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 254 2 19 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 254 (accept_3_2 37 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 254 2 18 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 254 2 17 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 254 2 16 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 254 (accept_3_2 31 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 254 2 15 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 66 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 254 2 14 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 254 2 13 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 254 (accept_3_2 25 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 254 2 12 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 66 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 254 2 11 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 254 2 10 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 254 (accept_3_2 19 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 254 2 9 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 254 2 8 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 254 2 7 33 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 254 (accept_3_2 13
  66 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 254 2 6 33 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 254
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 254 2 5 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 254 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 66 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 254 2 4 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 254 (accept_3_2 7 66 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 254 2 3 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 254 2 2 33 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  66 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 254 2 1 33 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 254 (accept_3_2 1 66
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 254 (allA_succ_of_accept 64 65 254
  (accept_3_2 64 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 254 (Polychromatic418967fa.accept_15_2_5_14_1_61 62 65 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 254 (accept_3_2 61 65 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 254 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 254 (accept_3_2 58 65
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 254 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 254
  (Polychromatic418967fa.accept_10_6_5_4_1_571 56 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 65 254 (accept_3_2 55 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  65 254 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 65 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 254 (accept_3_2 52 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 254
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 50 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 254 (accept_3_2 49 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 254 (Polychromatic418967fa.accept_20_8_5_14_1_3904 48 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 254 (accept_3_2 46 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 254 (accept_3_2 43 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 41 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 254 (accept_3_2 40 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 254
  (Polychromatic418967fa.accept_15_8_5_14_1_986 38 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 254 (accept_3_2 37 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 254 (accept_3_2 34 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 254 (accept_3_2 31 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 254 (Polychromatic418967fa.accept_19_11_8_7_1_11423 30 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 254 (Polychromatic418967fa.accept_10_9_5_4_1_966 29 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 254 (accept_3_2 28 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 254
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 254 (accept_3_2 25 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 254 (accept_3_2 22 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 254 (accept_3_2 19 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 254 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 254 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 254 (accept_3_2 16 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 254
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 254 (accept_3_2 13 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 254 (Polychromatic418967fa.accept_19_12_8_7_1_7209 12 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 254 (accept_3_2 10 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 254
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 254 (accept_3_2 7 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  254 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 254 (Polychromatic418967fa.accept_23_5_19_1_1_10609 5 65 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 254 (accept_3_2 4 65 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  2 65 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 254 (accept_3_2 1 65
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 254 (allA_of_3_0 64 64 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 254 (allA_succ_of_accept 62 63 254
  (Polychromatic418967fa.accept_15_2_3_14_1_972 62 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 254 (accept_3_2 61 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 254 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 254 (accept_3_2 58 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 254
  (Polychromatic418967fa.accept_13_4_11_7_1_558 56 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 254 (accept_3_2 55 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 254 (accept_3_2 52 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 254 (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 63 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 254
  (Polychromatic418967fa.accept_22_6_19_12_1_7667 50 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 254 (accept_3_2 49 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 254 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 254 (accept_3_2 46 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 254
  (Polychromatic418967fa.accept_13_5_11_7_1_559 44 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 254 (accept_3_2 43 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 254 (accept_3_2 40 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 254 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 63 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 254
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 38 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 254 (accept_3_2 37 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 254 (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 254 (accept_3_2 34 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 254
  (Polychromatic418967fa.accept_15_2_3_14_1_972 32 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 254 (accept_3_2 31 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 254 (accept_3_2 28 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 254 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 63 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 254
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 254 (accept_3_2 25 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 254 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 254 (accept_3_2 22 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 254
  (Polychromatic418967fa.accept_16_4_15_14_1_5056 20 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 254 (accept_3_2 19 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 254 (accept_3_2 16 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 254 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 63 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 254
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 254 (accept_3_2 13 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 254 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 254 (accept_3_2 10 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 254
  (Polychromatic418967fa.accept_19_8_6_7_1_7216 8 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 254 (accept_3_2 7 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  254 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 254 (accept_3_2 4 63 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 254 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 63 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 254 (Polychromatic418967fa.accept_15_2_3_14_1_972 2
  63 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 254 (accept_3_2 1 63 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 254 (allA_succ_of_accept 61 62 254
  (accept_3_2 61 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 254 2 30 31 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 254 2 29 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 62 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 254 2 28 31 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 254 (accept_3_2 55 62 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 254 2 27 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 53
  62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 254 2 26 31 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 254 2 25 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 254 (accept_3_2 49 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 254 2 24 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 62 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 254 2 23 31 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 254 2 22 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 254 (accept_3_2 43 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 254 2 21 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 254 2 20 31 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 254 2 19 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 254 (accept_3_2 37 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 254 2 18 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 254 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 62 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 254 2 17 31 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 254 2 16 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 254 (accept_3_2 31 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 254 2 15 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 62 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 254 2 14 31 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 254 2 13 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 254 (accept_3_2 25 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 254 2 12 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 62 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 254 2 11 31 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 254 2 10 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 254 (accept_3_2 19 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 254 2 9 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 62 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 254 2 8 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 254 2 7 31 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 254 (accept_3_2 13
  62 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 254 2 6 31 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 254 2 5 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 254 (Polychromatic418967fa.accept_19_9_5_7_1_5853 9 62 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 254 2 4 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 254 (accept_3_2 7 62 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 254 2 3 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 254 2 2 31 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 62
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 254 2 1 31 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 254 (accept_3_2 1 62
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 254 (allA_of_3_0 61 61 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 254 (allA_succ_of_accept 59 60 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 254 2 29 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 254 2 28 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 254 (accept_3_2 55 60 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 254 2 27 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 53
  60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 254 2 26 30 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 254
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 254 2 25 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 60 254 (accept_3_2 49 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 254 2 24 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 60 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 254 2 23 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 254
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 45 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 60 254 2 22 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 60 254 (accept_3_2 43 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 254 2 21 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 60 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 254 2 20 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 254 2 19 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 60 254 (accept_3_2 37 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 254 2 18 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 60 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 254 2 17 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 254 2 16 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 60 254 (accept_3_2 31 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 254 2 15 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 60 254 (Polychromatic418967fa.accept_13_3_8_7_1_4135 29 60 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 254 2 14 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 60 254 2 13 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 60 254 (accept_3_2 25 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 254 2 12 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 60 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 254 2 11 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 254 2 10 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 60 254 (accept_3_2 19 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 254 2 9 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 60 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 254 2 8 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 254 (Polychromatic418967fa.accept_13_2_8_7_1_2424
  15 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 254 2 7 30 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 254 (accept_3_2 13
  60 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 254 2 6 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 254
  (Polychromatic418967fa.accept_23_11_14_1_1_15490 11 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 254 2 5 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 60 254 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 60 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 254 2 4 30 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 254 (accept_3_2 7 60 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 254 2 3 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 254 2 2 30 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 254 2 1 30 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 254 (accept_3_2 1 60 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 254 (allA_succ_of_accept 58 59 254
  (accept_3_2 58 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 59 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 254 (accept_3_2 55 59 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 254 (accept_3_2 52 59
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 254 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 254 (accept_3_2 49 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 254 (accept_3_2 46 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 254 (accept_3_2 43 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 254 (accept_3_2 40 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 254
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 254 (accept_3_2 37 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 254 (accept_3_2 34 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 254 (accept_3_2 31 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 254 (accept_3_2 28 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 254 (accept_3_2 25 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 254 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 254 (accept_3_2 22 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 254 (accept_3_2 19 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 254 (accept_3_2 16 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 254
  (Polychromatic418967fa.accept_17_14_8_16_1_6863 14 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 254 (accept_3_2 13 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 254 (Polychromatic418967fa.accept_21_11_17_2_1_4749 11 59 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 254 (accept_3_2 10 59 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 254 (accept_3_2 7 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 254 (accept_3_2 4 59 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 254 (Polychromatic418967fa.accept_17_2_8_16_1_4403
  2 59 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 254 (accept_3_2 1 59
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  254))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 254 (allA_of_3_0 58 58 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 57 254 (allA_succ_of_accept 56 57 254
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 56 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 57 254 (accept_3_2 55 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 254 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 57 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 254 (accept_3_2 52 57 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 254 (accept_3_2 49 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 254 (accept_3_2 46 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 254 (accept_3_2 43 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 254 (accept_3_2 40 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 254 (accept_3_2 37 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 254 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 254 (accept_3_2 34 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 254 (accept_3_2 31 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 254 (accept_3_2 28 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 254 (accept_3_2 25 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 254 (accept_3_2 22 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 254 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 57 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 254 (accept_3_2 19 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 254 (accept_3_2 16 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 254 (accept_3_2 13 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 254 (accept_3_2 10 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 57 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 254 (accept_3_2 7 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 254 (accept_3_2 4 57 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  57 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 254 (accept_3_2 1 57 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 254 (allA_succ_of_accept 55 56 254 (accept_3_2 55 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 254 2 27 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 56 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 56 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 254 2 26 28 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 254
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 51 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 56 254 2 25 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 56 254 (accept_3_2 49 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 56 254 2 24 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 56 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 56 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 254 2 23 28 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 254 2 22 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 56 254 (accept_3_2 43 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 56 254 2 21 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 56 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 56 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 254 2 20 28 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 254
  (Polychromatic418967fa.accept_19_1_18_7_1_12744 39 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 254 2 19 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 56 254 (accept_3_2 37 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 56 254 2 18 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 56 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 56 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 254 2 17 28 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 254
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 33 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 254 2 16 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 56 254 (accept_3_2 31 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 56 254 2 15 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 56 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 254 2 14 28 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 254
  (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 56 254 2 13 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 56 254 (accept_3_2 25 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 56 254 2 12 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 56 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 56 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 254 2 11 28 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 254
  (Polychromatic418967fa.accept_17_4_5_16_1_3240 21 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 254 2 10 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 56 254 (accept_3_2 19 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 56 254 2 9 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 56 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 56 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 254 2 8 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  56 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 254 2 7 28 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 254 (accept_3_2 13
  56 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 254 2 6 28 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 254
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 56 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 56 254 2 5 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 56 254 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 56 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 254 2 4 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 254 (accept_3_2 7 56 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 56 254 2 3 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 56 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 56 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 254 2 2 28 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 254 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3
  56 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 254 2 1 28 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 254 (accept_3_2 1 56
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 254))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 254 (allA_of_3_0 55 55 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 254
  (allA_succ_of_accept 53 54 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 54 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 254 2 26 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 51
  54 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 254 2 25 27 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 254 (accept_3_2 49
  54 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 254 2 24 27 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 254
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 47 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 254 2 23 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 54 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 54 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 254 2 22 27 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 254 (accept_3_2 43 54 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 254 2 21 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 254 (Polychromatic418967fa.accept_17_7_3_16_1_2208
  41 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 254 2 20 27 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 254 2 19 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 54 254 (accept_3_2 37 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 254 2 18 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 54 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 254 2 17 27 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 254 2 16 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 54 254 (accept_3_2 31 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 254 2 15 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 254 (Polychromatic418967fa.accept_19_10_16_7_1_10039 29 54 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 254 2 14 27 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 254 2 13 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 254 (accept_3_2 25 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 254 2 12 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 254 (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 54 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 254 2 11 27 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 254 2 10 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 254 (accept_3_2 19 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 254 2 9 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 54 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 254 2 8 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 15
  54 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 254 2 7 27 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 254 (accept_3_2 13
  54 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 254 2 6 27 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 54 254 2 5 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 54 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 54 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 254 2 4 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 254 (accept_3_2 7 54 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 54 254 2 3 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 54 254 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 54 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 254 2 2 27 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 254 2 1 27 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 254 (accept_3_2 1 54
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 254))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 254 (allA_succ_of_accept 52 53 254 (accept_3_2 52 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 53 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 53 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 53 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 254 (accept_3_2 49 53 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 48
  53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 254 (accept_3_2 46 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 254 (accept_3_2 43 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 254 (accept_3_2 40 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 254 (Polychromatic418967fa.accept_21_17_11_2_1_7953 38 53 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 254 (accept_3_2 37 53 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 254 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 53
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 254 (accept_3_2 34 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 254 (accept_3_2 31 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 53 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 254
  (Polychromatic418967fa.accept_10_9_3_4_1_985 29 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 254 (accept_3_2 28 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 254 (accept_3_2 25 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 254 (accept_3_2 22 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 254 (accept_3_2 19 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 254 (Polychromatic418967fa.accept_17_1_2_16_1_5596 18 53 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 254
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 254 (accept_3_2 16 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 254 (accept_3_2 13 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 254 (accept_3_2 10 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 254 (accept_3_2 7 53 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 254 (accept_3_2 4 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 254 (Polychromatic418967fa.accept_23_2_7_1_1_15489 2 53 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 254 (accept_3_2 1 53 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 254))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 254 (allA_of_3_0 52 52
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 254 (allA_succ_of_accept 50 51 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 254 (accept_3_2 49 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 254 (accept_3_2 46 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 51 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 254 (accept_3_2 43 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 254 (accept_3_2 40 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 254
  (Polychromatic418967fa.accept_15_8_6_14_1_975 38 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 254 (accept_3_2 37 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 254 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 254 (accept_3_2 34 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 254 (accept_3_2 31 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 254 (accept_3_2 28 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 254 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 51 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 254 (accept_3_2 25 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 254 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 254 (accept_3_2 22 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 254
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 254 (accept_3_2 19 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 254 (accept_3_2 16 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 254 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 51 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 254 (accept_3_2 13 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 254 (accept_3_2 10 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 254 (accept_3_2 7 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  254 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 254 (accept_3_2 4 51 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 254 (Polychromatic418967fa.accept_19_2_13_7_1_7211
  2 51 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 254 (accept_3_2 1 51
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 254)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 254 (allA_succ_of_accept 49 50 254 (accept_3_2 49 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 254 2 24 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 50 254 (Polychromatic418967fa.accept_15_2_5_14_1_61 47 50 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 254 2 23 25 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 50 254 2 22 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 50 254 (accept_3_2 43 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 50 254 2 21 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 50 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 50 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 254 2 20 25 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 254 2 19 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 50 254 (accept_3_2 37 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 254 2 18 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 254 2 17 25 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 254 2 16 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 254 (accept_3_2 31 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 254 2 15 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 254 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 50 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 254 2 14 25 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 50 254 2 13 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 50 254 (accept_3_2 25 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 254 2 12 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 254 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 50 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 254 2 11 25 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 254 2 10 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 254 (accept_3_2 19 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 254 2 9 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 50 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 254 2 8 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  50 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 254 2 7 25 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 254 (accept_3_2 13
  50 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 254 2 6 25 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 254
  (Polychromatic418967fa.accept_18_11_14_2_1_5058 11 50 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 254 2 5 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 254 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 50 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 254 2 4 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 254 (accept_3_2 7 50 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 254 2 3 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 254 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 50 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 254 2 2 25 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 50
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 254 2 1 25 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 254 (accept_3_2 1 50
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 254))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 254 (allA_of_3_0 49 49 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 254
  (allA_succ_of_accept 47 48 254 (Polychromatic418967fa.accept_13_8_9_7_1_530 47 48 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 254 2 23 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 45
  48 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 254 2 22 24 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 254 (accept_3_2 43
  48 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 254 2 21 24 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 254 2 20 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 48 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 254 2 19 24 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 254 (accept_3_2 37 48 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 254 2 18 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35
  48 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 254 2 17 24 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 254 2 16 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 254 (accept_3_2 31 48 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 254 2 15 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 48 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 254 2 14 24 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 254
  (Polychromatic418967fa.accept_22_5_4_12_1_15488 27 48 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 254 2 13 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 48 254 (accept_3_2 25 48 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 254 2 12 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 48 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 254 2 11 24 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 254
  (Polychromatic418967fa.accept_13_8_9_7_1_530 21 48 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 254 2 10 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 254 (accept_3_2 19 48 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 254 2 9 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 254 2 8 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  48 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 254 2 7 24 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 254 (accept_3_2 13
  48 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 254 2 6 24 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 48 254 2 5 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 48 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 48 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 254 2 4 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 254 (accept_3_2 7 48 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 48 254 2 3 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 48 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 254 2 2 24 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 254 2 1 24 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 254 (accept_3_2 1 48
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 254))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 47 254 (allA_succ_of_accept 46 47 254 (accept_3_2 46 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 47 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 47 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 47
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 254 (accept_3_2 43 47 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 254 (Polychromatic418967fa.accept_10_2_7_4_1_967
  42 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 254 (accept_3_2 40 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 254 (accept_3_2 37 47 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 254 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 47 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 254
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 254 (accept_3_2 34 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 254 (accept_3_2 31 47 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 254 (Polychromatic418967fa.accept_19_11_9_7_1_4447 30 47 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 254 (accept_3_2 28 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 254 (Polychromatic418967fa.accept_16_10_15_14_1_1086 26 47 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 254 (accept_3_2 25 47 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 254
  (Polychromatic418967fa.accept_10_3_7_4_1_584 23 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 254 (accept_3_2 22 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 47 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 254 (accept_3_2 19 47 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 254 (accept_3_2 16 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 254 (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 47 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 254 (accept_3_2 13 47 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 47 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 254 (accept_3_2 10 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 47 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 47 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 254 (accept_3_2 7 47 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 47 254 (Polychromatic418967fa.accept_25_6_22_4_1_13669 6 47 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 254 (accept_3_2 4 47 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 254 (accept_3_2 1 47 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  254))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 254 (allA_of_3_0 46 46 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 254 (allA_succ_of_accept 44 45 254 (Polychromatic418967fa.accept_23_21_22_1_1_12147
  44 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 254 (accept_3_2 43
  45 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 254
  (Polychromatic418967fa.accept_12_6_9_2_1_311 42 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 254 (accept_3_2 40 45 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 254 (Polychromatic418967fa.accept_13_12_6_7_1_1071
  38 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 254 (accept_3_2 37
  45 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 254 (accept_3_2 34 45 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 254
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 32 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 45 254 (accept_3_2 31 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 45 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 45 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 254 (accept_3_2 28 45 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 254 (accept_3_2 25 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 254 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 254 (accept_3_2 22 45 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 254 (accept_3_2 19 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 254 (accept_3_2 16 45 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 254
  (Polychromatic418967fa.accept_13_1_6_7_1_550 14 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 254 (accept_3_2 13 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 254 (accept_3_2 10 45 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 254 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 45 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 254 (accept_3_2 7 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 254 (accept_3_2 4 45 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 254 (Polychromatic418967fa.accept_22_2_1_12_1_13867
  2 45 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 254 (accept_3_2 1 45
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 254))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  44 254 (allA_succ_of_accept 43 44 254 (accept_3_2 43 44 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  42 44 254 2 21 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 44 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 254 2 20 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 39
  44 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 254 2 19 22 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 254 (accept_3_2 37
  44 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 254 2 18 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 254
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 44 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 254 2 17 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 44 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 44 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 254 2 16 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 254 (accept_3_2 31 44 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 254 2 15 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 29
  44 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 254 2 14 22 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 254
  (Polychromatic418967fa.accept_19_8_6_7_1_7216 27 44 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 254 2 13 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 254 (accept_3_2 25 44 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 254 2 12 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 44 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 254 2 11 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 44 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 254 2 10 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 44 254 (accept_3_2 19 44 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 44 254 2 9 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 44 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 44 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 254 2 8 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  44 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 254 2 7 22 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 254 (accept_3_2 13
  44 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 254 2 6 22 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 254
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 44 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 44 254 2 5 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 44 254 (Polychromatic418967fa.accept_17_9_10_16_1_3217 9 44 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 254 2 4 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 254 (accept_3_2 7 44 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 44 254 2 3 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 44 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 254 2 2 22 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 44
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 254 2 1 22 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 254 (accept_3_2 1 44
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 254)))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  43 254 (allA_of_3_0 43 43 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 254 (allA_succ_of_accept 41 42
  254 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 254 2 20 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 254 2 19 21 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 254 (accept_3_2 37 42 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 254 2 18 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 35
  42 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 254 2 17 21 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 254 2 16 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 254 (accept_3_2 31 42 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 254 2 15 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 254 (Polychromatic418967fa.accept_16_13_10_14_1_2871 29 42 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 254 2 14 21 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 42 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 254 2 13 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 254 (accept_3_2 25 42 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 254 2 12 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 254 2 11 21 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 254 2 10 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 42 254 (accept_3_2 19 42 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 254 2 9 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 254 2 8 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 15
  42 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 254 2 7 21 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 254 (accept_3_2 13
  42 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 254 2 6 21 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 254
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 42 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 254 2 5 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 254 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 42 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 254 2 4 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 254 (accept_3_2 7 42 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 42 254 2 3 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 42 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 254 2 2 21 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 254 2 1 21 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 254 (accept_3_2 1 42
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 254)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41
  254 (allA_succ_of_accept 40 41 254 (accept_3_2 40 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 41 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 254 (accept_3_2 37 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 254 (accept_3_2 34 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 254 (accept_3_2 31 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 41 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 254 (accept_3_2 28 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 254 (accept_3_2 25 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 254 (accept_3_2 22 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 254 (accept_3_2 19 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 254 (accept_3_2 16 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 254 (Polychromatic418967fa.accept_19_14_3_7_1_7248 14 41 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 254 (accept_3_2 13 41 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 41 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 254 (accept_3_2 10 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 254 (accept_3_2 7 41 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 254
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 254 (accept_3_2 4 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 254 (Polychromatic418967fa.accept_22_2_19_12_1_7598 2 41 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 254 (accept_3_2 1 41 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 254))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 254 (allA_of_3_0 40 40 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 254 (allA_succ_of_accept 38 39 254
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 254 (accept_3_2 37 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 254 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 254 (accept_3_2 34 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 254 (accept_3_2 31 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 254 (accept_3_2 28 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 254 (accept_3_2 25 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 254 (accept_3_2 22 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 254 (accept_3_2 19 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 254 (accept_3_2 16 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 254 (accept_3_2 13 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 254 (accept_3_2 10 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 254 (accept_3_2 7 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 254 (accept_3_2 4 39 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 254 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 39 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 254 (Polychromatic418967fa.accept_17_2_5_16_1_1264
  2 39 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 254 (accept_3_2 1 39
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 254))))))))))))))))))))))))))))))))))))))) (allB_succ 38 254
  (allA_succ_of_accept 37 38 254 (accept_3_2 37 38 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  254 2 18 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 254 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 38 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 254 2 17 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 38 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 254 2 16 19 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 254 (accept_3_2 31 38 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 254 2 15 19 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 254 2 14 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 38 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 254 2 13 19 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 254 (accept_3_2 25 38 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 254 2 12 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 254 (Polychromatic418967fa.accept_13_10_12_7_1_1079
  23 38 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 254 2 11 19 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 254
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 38 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 254 2 10 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 38 254 (accept_3_2 19 38 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 254 2 9 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 254 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 38 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 254 2 8 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  38 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 254 2 7 19 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 254 (accept_3_2 13
  38 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 254 2 6 19 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 254
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 38 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 254 2 5 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 38 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 254 2 4 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 254 (accept_3_2 7 38 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 254 2 3 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 254 2 2 19 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 254 (Polychromatic418967fa.accept_17_3_4_16_1_3208 3
  38 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 254 2 1 19 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 254 (accept_3_2 1 38
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 254)))))))))))))))))))))))))))))))))))))) (allB_succ 37 254
  (allA_of_3_0 37 37 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 254 (allA_succ_of_accept 35 36 254
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 36 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 254 2 17 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 36 254 (Polychromatic418967fa.accept_16_1_4_14_1_1896 33 36 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 254 2 16 18 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 254 (accept_3_2 31 36 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 254 2 15 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 254 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  29 36 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 254 2 14 18 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 254 2 13 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 254 (accept_3_2 25 36 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 254 2 12 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 36 254 (Polychromatic418967fa.accept_15_8_6_14_1_975 23 36 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 254 2 11 18 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 254
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 36 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 36 254 2 10 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 254 (accept_3_2 19 36 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 254 2 9 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 254 2 8 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  36 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 254 2 7 18 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 254 (accept_3_2 13
  36 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 254 2 6 18 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 254
  (Polychromatic418967fa.accept_22_11_14_12_1_7700 11 36 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 254 2 5 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 36 254 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 36 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 254 2 4 18 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 254 (accept_3_2 7 36 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 254 2 3 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 36 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 254 2 2 18 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 254 2 1 18 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 254 (accept_3_2 1 36 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  254)))))))))))))))))))))))))))))))))))) (allB_succ 35 254 (allA_succ_of_accept 34 35 254 (accept_3_2 34 35 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 254 (accept_3_2 31 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 254 (accept_3_2 28 35 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 254
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 254 (accept_3_2 25 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 35 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 254 (accept_3_2 22 35 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 254 (accept_3_2 19 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 254 (Polychromatic418967fa.accept_25_18_10_4_1_15487 18 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 254 (accept_3_2 16 35 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 254 (accept_3_2 13 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 35 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 254 (accept_3_2 10 35 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 254 (accept_3_2 7 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  254 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 254 (accept_3_2 4 35 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 254 (Polychromatic418967fa.accept_13_2_9_7_1_164 2
  35 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 254 (accept_3_2 1 35 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 254))))))))))))))))))))))))))))))))))) (allB_succ 34 254
  (allA_of_3_0 34 34 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 254 (allA_succ_of_accept 32 33 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 254 (accept_3_2 31 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 254 (accept_3_2 28 33 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 254 (accept_3_2 25 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 254 (accept_3_2 22 33 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 254
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 20 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 254 (accept_3_2 19 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 254 (accept_3_2 16 33 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 254 (accept_3_2 13 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 254 (accept_3_2 10 33 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 254 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 33 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 254 (accept_3_2 7 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  254 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 254 (accept_3_2 4 33 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 254 (Polychromatic418967fa.accept_15_2_3_14_1_972 2
  33 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 254 (accept_3_2 1 33 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 254))))))))))))))))))))))))))))))))) (allB_succ 32 254
  (allA_succ_of_accept 31 32 254 (accept_3_2 31 32 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  254 2 15 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 32 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 32 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 254 2 14 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 32 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 32 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 254 2 13 16 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 254 (accept_3_2 25 32 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 254 2 12 16 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 254
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 32 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 32 254 2 11 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 32 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 32 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 254 2 10 16 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 254 (accept_3_2 19 32 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 254 2 9 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  32 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 254 2 8 16 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 32 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 32 254 2 7 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 32 254 (accept_3_2 13 32 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32
  254 2 6 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  32 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 32 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 32 254 2 5 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 32 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 32 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 254 2 4 16 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 254 (accept_3_2 7 32 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 254 2 3 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 254 2 2 16 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 32 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 254 2 1 16 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 254 (accept_3_2 1 32 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  254)))))))))))))))))))))))))))))))) (allB_succ 31 254 (allA_of_3_0 31 31 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 30 254 (allA_succ_of_accept 29 30 254 (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 30 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 254 2 14 15 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 30 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 254 2 13 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 30 254 (accept_3_2 25 30 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 30 254 2 12 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 30 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 254 2 11 15 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 254 2 10 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 254 (accept_3_2 19 30 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 254 2 9 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 30 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 254 2 8 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  30 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 254 2 7 15 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 254 (accept_3_2 13
  30 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 254 2 6 15 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 254
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 30 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 254 2 5 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 254 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 30 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 254 2 4 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 254 (accept_3_2 7 30 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 254 2 3 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 30 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 254 2 2 15 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 3
  30 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 254 2 1 15 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 254 (accept_3_2 1 30
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 254)))))))))))))))))))))))))))))) (allB_succ 29 254
  (allA_succ_of_accept 28 29 254 (accept_3_2 28 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 254 (Polychromatic418967fa.accept_16_10_13_14_1_5042 26 29 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 254 (accept_3_2 25 29 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 254 (accept_3_2 22 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 254 (accept_3_2 19 29 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 29 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 254 (accept_3_2 16 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 254 (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 29 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 254 (accept_3_2 13 29 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 254 (Polychromatic418967fa.accept_26_12_3_20_1_15486 12 29 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 254 (accept_3_2 10 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 29 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 254 (accept_3_2 7 29 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 254
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 254 (accept_3_2 4 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 254 (Polychromatic418967fa.accept_23_2_6_1_1_15485 2 29 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 254 (accept_3_2 1 29 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 254))))))))))))))))))))))))))))) (allB_succ 28 254 (allA_of_3_0 28 28 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 254 (allA_succ_of_accept 26 27 254 (Polychromatic418967fa.accept_15_11_12_14_1_2612
  26 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 254 (accept_3_2 25
  27 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 254 (accept_3_2 22 27 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 254 (Polychromatic418967fa.accept_19_1_8_7_1_4470
  20 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 254 (accept_3_2 19
  27 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 254 (accept_3_2 16 27 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 254
  (Polychromatic418967fa.accept_19_14_8_7_1_12706 14 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 254 (accept_3_2 13 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 254 (accept_3_2 10 27 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 254 (accept_3_2 7 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  254 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 27 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 254 (accept_3_2 4 27 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  27 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 254 (accept_3_2 1 27 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 254))))))))))))))))))))))))))) (allB_succ 26 254
  (allA_succ_of_accept 25 26 254 (accept_3_2 25 26 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  254 2 12 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 26 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 26 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 254 2 11 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 26 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 254 2 10 13 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 254 (accept_3_2 19 26 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 254 2 9 13 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 26 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 26 254 2 8 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 26 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 26 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 254 2 7 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 254 (accept_3_2 13 26 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 254 2 6 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 26 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 254 2 5 13 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 254
  (Polychromatic418967fa.accept_20_9_6_14_1_11239 9 26 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 254 2 4 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 254 (accept_3_2 7 26 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 254
  2 3 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 26 254 2 2 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 26 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 26 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 254 2 1 13 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 254 (accept_3_2 1 26 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 254)))))))))))))))))))))))))) (allB_succ 25 254 (allA_of_3_0 25 25 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 254 (allA_succ_of_accept 23 24 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23
  24 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 254 2 11 12 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 254 2 10 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 24 254 (accept_3_2 19 24 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 254 2 9 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 254 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 254 2 8 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  24 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 254 2 7 12 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 254 (accept_3_2 13
  24 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 254 2 6 12 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 254
  (Polychromatic418967fa.accept_25_11_24_4_1_15484 11 24 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 24 254 2 5 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 24 254 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 24 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 254 2 4 12 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 254 (accept_3_2 7 24 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 254 2 3 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 254 2 2 12 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 24 254 2 1 12 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 254 (accept_3_2 1 24 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  254)))))))))))))))))))))))) (allB_succ 23 254 (allA_succ_of_accept 22 23 254 (accept_3_2 22 23 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 254
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 254 (accept_3_2 19 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 254 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 23 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 254 (accept_3_2 16 23 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 254
  (Polychromatic418967fa.accept_19_14_4_7_1_8728 14 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 254 (accept_3_2 13 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 254 (Polychromatic418967fa.accept_14_11_9_2_1_6382 11 23 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 254 (accept_3_2 10 23 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 254 (accept_3_2 7 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  254 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 254 (accept_3_2 4 23 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 254 (Polychromatic418967fa.accept_19_2_4_7_1_10048
  2 23 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 254 (accept_3_2 1 23
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 254))))))))))))))))))))))) (allB_succ 22 254 (allA_of_3_0 22
  22 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 254 (allA_succ_of_accept 20 21 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 254 (accept_3_2 19 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 254 (accept_3_2 16 21 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 254 (accept_3_2 13 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 254 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 254 (accept_3_2 10 21 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 254 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 21 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 254 (accept_3_2 7 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  254 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 254 (accept_3_2 4 21 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 254 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  2 21 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 254 (accept_3_2 1 21
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 254))))))))))))))))))))) (allB_succ 20 254
  (allA_succ_of_accept 19 20 254 (accept_3_2 19 20 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20
  254 2 9 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  20 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 254 2 8 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 20 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 20 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 254 2 7 10 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 254 (accept_3_2 13 20 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 254 2 6 10 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 254
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 254 2 5 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 254 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 20 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 254 2 4 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 254 (accept_3_2 7 20 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 20 254 2 3 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 20 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 20 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 20 254 2 2 10 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 20 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 20
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 254 2 1 10 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 254 (accept_3_2 1 20
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 254)))))))))))))))))))) (allB_succ 19 254 (allA_of_3_0 19 19
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 18 254 (allA_succ_of_accept 17 18 254
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 18 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 18 254 2 8 9 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 18 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 18 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 18 254 2 7 9 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 254 (accept_3_2 13 18 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 18 254 2 6 9 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 18 254 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 18 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 254 2 5 9 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 9
  18 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 254 2 4 9 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 254 (accept_3_2 7 18
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 254 2 3 9 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 18 254 2 2 9 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 18 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 18 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 254 2 1 9 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 254 (accept_3_2 1 18 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 18 254)))))))))))))))))) (allB_succ 17 254 (allA_succ_of_accept 16 17 254 (accept_3_2 16 17 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  17 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 254 (accept_3_2 13 17 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 254 (accept_3_2 10 17 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 254 (accept_3_2 7 17 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 254 (accept_3_2 4 17 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  17 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 254 (accept_3_2 1 17 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 254))))))))))))))))) (allB_succ 16 254 (allA_of_3_0 16 16 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 254 (allA_succ_of_accept 14 15 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 15 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 254 (accept_3_2 13 15 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 15 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 254 (accept_3_2 10 15 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 15 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 254 (accept_3_2 7 15 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 254 (accept_3_2 4 15 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 254 (Polychromatic418967fa.accept_25_2_15_4_1_15483
  2 15 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 254 (accept_3_2 1 15
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 254))))))))))))))) (allB_succ 14 254 (allA_succ_of_accept 13
  14 254 (accept_3_2 13 14 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 254 2 6 7 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 254
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 14 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 254 2 5 7 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 254 (Polychromatic418967fa.accept_21_9_14_2_1_6370 9 14 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 254 2 4 7 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 254 (accept_3_2 7 14 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 254 2 3 7 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 254 (Polychromatic418967fa.accept_27_5_14_11_1_15482 5 14 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 254 2 2 7 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 14
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 254 2 1 7 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 254 (accept_3_2 1 14
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 254)))))))))))))) (allB_succ 13 254 (allA_of_3_0 13 13 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 254 (allA_succ_of_accept 11 12 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 254 2 5 6 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 12 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 254 2 4 6 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 254 (accept_3_2 7 12 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 254 2 3 6 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 254 2 2 6 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 254 2 1 6 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 254 (accept_3_2 1 12
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 254)))))))))))) (allB_succ 11 254 (allA_succ_of_accept 10 11
  254 (accept_3_2 10 11 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 11 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 254 (accept_3_2 7 11 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 254 (accept_3_2 4 11 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 254
  (Polychromatic418967fa.accept_25_2_11_4_1_15481 2 11 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 254 (accept_3_2 1 11 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  254))))))))))) (allB_succ 10 254 (allA_of_3_0 10 10 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 254
  (allA_succ_of_accept 8 9 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 9 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 254 (accept_3_2 7 9 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 9 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 254 (accept_3_2 4 9 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 254
  (Polychromatic418967fa.accept_13_2_9_7_1_164 2 9 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 254 (accept_3_2 1 9 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 254)))))))))
  (allB_succ 8 254 (allA_succ_of_accept 7 8 254 (accept_3_2 7 8 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 254 2 3 4 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 254 2 2 4 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 254 2 1 4 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 254 (accept_3_2 1 8 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 254)))))))) (allB_succ 7 254 (allA_of_3_0 7 7 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 254 (allA_succ_of_accept 5 6 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 254 2 2 3 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 254 2 1 3 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 254 (accept_3_2 1 6 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 254))))))
  (allB_succ 5 254 (allA_succ_of_accept 4 5 254 (accept_3_2 4 5 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 254 (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 5 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 254 (accept_3_2 1 5 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 254))))) (allB_succ 4 254 (allA_of_3_0 4 4 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 254 (allA_succ_of_accept 2 3 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 3
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 254 (accept_3_2 1 3 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 254))) (allB_succ 2 254 (allA_succ_of_accept 1 2 254 (accept_3_2
  1 2 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 254)) (allB_two
  254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


