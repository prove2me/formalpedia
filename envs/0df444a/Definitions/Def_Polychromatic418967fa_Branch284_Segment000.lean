-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch284_Segment000
-- name    : Polychromatic418967fa_Branch284_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:53:32.699705+00:00
-- url     : https://prove2.me/theorems/483a84e5-69a8-4140-8abe-20df7eb89045
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

def Polychromatic418967fa.branch_284_segment_000 : allB 123 284 :=
  allB_succ 122 284 (allA_succ_of_accept 121 122 284 (accept_3_2 121 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 122 284 2 60 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 122 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 119 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 122 284 2 59 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 122 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 117 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 122 284 2 58 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 122 284 (accept_3_2 115 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 122 284 2 57 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 122 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 113 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 122 284 2 56 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 122 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 111 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 122 284 2 55 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 122 284 (accept_3_2 109 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 122 284 2 54 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 122 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 107 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 122 284 2 53 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 122 284
  (Polychromatic418967fa.accept_14_7_10_4_1_130 105 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 122 284 2 52 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 122 284 (accept_3_2 103 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 122 284 2 51 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 122 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 101 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 122 284 2 50 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 122 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 99 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 122 284 2 49 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 122 284 (accept_3_2 97 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 122 284 2 48 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 122 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 122 284 2 47 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 122 284
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 93 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 122 284 2 46 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 122 284 (accept_3_2 91 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 122 284 2 45 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 122 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 122 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 122 284 2 44 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 122 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 87 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 122 284 2 43 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 122 284 (accept_3_2 85 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 122 284 2 42 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 122 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 122 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 122 284 2 41 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 122 284
  (Polychromatic418967fa.accept_13_3_5_11_1_716 81 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 122 284 2 40 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 122 284 (accept_3_2 79 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 122 284 2 39 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 122 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 122 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 122 284 2 38 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 122 284
  (Polychromatic418967fa.accept_16_11_10_12_1_4832 75 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 122 284 2 37 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 122 284 (accept_3_2 73 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 122 284 2 36 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 122 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 122 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 122 284 2 35 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 122 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 122 284 2 34 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 122 284 (accept_3_2 67 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 122 284 2 33 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 122 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 65 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 284 2 32 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 284
  (Polychromatic418967fa.accept_14_7_10_4_1_130 63 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 284 2 31 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 284 (accept_3_2 61 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 284 2 30 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 284 2 29 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 284 2 28 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 284 (accept_3_2 55 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 284 2 27 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 122 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 284 2 26 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 284
  (Polychromatic418967fa.accept_16_3_10_12_1_4814 51 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 122 284 2 25 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 122 284 (accept_3_2 49 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 284 2 24 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 122 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 284 2 23 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 284
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 284 2 22 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 284 (accept_3_2 43 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 284 2 21 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 122 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 284 2 20 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 284
  (Polychromatic418967fa.accept_19_1_8_18_1_6667 39 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 284 2 19 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 284 (accept_3_2 37 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 284 2 18 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 284 2 17 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 284
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 284 2 16 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 284 (accept_3_2 31 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 284 2 15 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 122 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 284 2 14 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 284 2 13 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 284 (accept_3_2 25 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 284 2 12 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 284 2 11 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 284
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 284 2 10 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 284 (accept_3_2 19 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 284 2 9 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 122 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 122 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 284 2 8 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 284 2 7 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 122 284 (accept_3_2 13 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 122 284 2 6 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 122 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 284 2 5 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 284
  (Polychromatic418967fa.accept_19_9_8_18_1_1571 9 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 284 2 4 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 284 (accept_3_2 7 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  284 2 3 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 122 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 284 2 2 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 122 284 (Polychromatic418967fa.accept_13_3_5_11_1_716 3 122 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 284 2 1 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 284 (accept_3_2 1 122 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 121 284 (allA_of_3_0 121 121 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 120 284
  (allA_succ_of_accept 119 120 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 119 120 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 120 284 2 59 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 120 284 (Polychromatic418967fa.accept_7_5_1_4_1_122
  117 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 120 284 4 29 30 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 120 284
  (accept_3_2 115 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 120 284 2 57 60 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 120 284
  (Polychromatic418967fa.accept_16_1_8_12_1_405 113 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 120 284 4 28 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 120 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 111 120 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 120 284 2 55 60 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 120 284 (accept_3_2 109 120 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 120 284 4 27 30 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 120 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 107 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 120 284 2 53 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 120 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 120 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 120 284 4 26 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 284 (accept_3_2 103 120 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 120 284 2 51 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 120 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 101 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 284 4 25 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 120 284 (Polychromatic418967fa.accept_13_8_3_11_1_3467 99 120 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 120 284 2 49 60 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 284 (accept_3_2 97 120 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 120 284 4 24 30 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 120 284
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 95 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 120 284 2 47 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 120 284 (Polychromatic418967fa.accept_13_2_3_11_1_1287 93 120 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 284 4 23 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 284 (accept_3_2 91 120 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 120 284 2 45 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 120 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 89 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 120 284 4 22 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 120 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 120 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 120 284 2 43 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 120 284 (accept_3_2 85 120 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 120 284 4 21 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 120 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 83
  120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 284 2 41 60 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 284
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 81 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 120 284 4 20 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 120 284 (accept_3_2 79 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 120 284 2 39 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 120 284 (Polychromatic418967fa.accept_16_13_8_12_1_2723 77 120 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 284 4 19 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 120 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 120 284 2 37 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 120 284 (accept_3_2 73 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 284 4 18 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 120 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 120 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 284 2 35 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 120 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 120 284 4 17 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 120 284 (accept_3_2 67 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 284 2 33 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 120 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 284 4 16 30 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 284
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 120 284 2 31 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 284 (accept_3_2 61 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 284 4 15 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 120 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 284 2 29 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 284
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 57 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 120 284 4 14 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 120 284 (accept_3_2 55 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 284 2 27 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 120 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 284 4 13 30 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 120 284 2 25 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 120 284 (accept_3_2 49 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 284 4 12 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 120 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 284 2 23 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 120 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 120 284 4 11 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 120 284 (accept_3_2 43 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 284 2 21 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 284 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 120 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 284 4 10 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 284
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 120 284 2 19 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 120 284 (accept_3_2 37 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 284 4 9 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 120 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 284 2 17 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33
  120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 284 4 8 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 284 (accept_3_2 31
  120 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 284 2 15 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 284 4 7 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 120 284 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 120 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 284 2 13 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 284 (accept_3_2 25 120 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 284 4 6 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 120
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 284 2 11 60 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 284
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 284 4 5 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 284 (accept_3_2 19 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  120 284 2 9 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 120 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 284 4 4 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 284 2 7 60 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 284 (accept_3_2 13
  120 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 284 4 3 30 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 284 2 5 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 120 284 (Polychromatic418967fa.accept_16_9_8_12_1_979 9 120 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 284 4 2 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 284 (accept_3_2 7 120 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 284 2 3 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 120 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 284 4 1 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 120 284 2 1 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 284 (accept_3_2 1 120 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 284 (allA_succ_of_accept 118 119 284 (accept_3_2 118 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 119 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 116 119
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 119 284 (accept_3_2 115 119
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 119 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 114 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 119 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 113 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 119 284 (accept_3_2 112 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 119 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 110 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 119 284 (accept_3_2 109 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 119 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 108 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 119 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 107 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 119 284 (accept_3_2 106 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 119
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 119 284
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 104 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 119 284 (accept_3_2 103 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 119 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 119 284 (Polychromatic418967fa.accept_13_10_2_11_1_1920 101
  119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 119 284 (accept_3_2 100
  119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 119 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 99 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 119 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 119 284 (accept_3_2 97 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 119 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 119 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420
  95 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 119 284 (accept_3_2 94
  119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 119 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 93 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 119 284 (Polychromatic418967fa.accept_18_2_11_14_1_69 92 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 119 284 (accept_3_2 91 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 119 284 (Polychromatic418967fa.accept_21_6_14_11_1_10103 90 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 119 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 89 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 119 284 (accept_3_2 88 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 119 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 86 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 119 284 (accept_3_2 85 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 119 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 119 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 119 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 83 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 119 284 (accept_3_2 82 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 119 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 119 284 (accept_3_2 79 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 119 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 284
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 77 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 119 284 (accept_3_2 76 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 119
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 284 (accept_3_2 73 119
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 284
  (Polychromatic418967fa.accept_16_8_7_12_1_7207 72 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 119 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 284 (accept_3_2 70 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 284 (Polychromatic418967fa.accept_10_8_9_4_1_961
  68 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 284 (accept_3_2 67
  119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 66 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 119 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 65 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 284 (accept_3_2 64 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 284 (Polychromatic418967fa.accept_9_8_2_5_1_237
  62 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 284 (accept_3_2 61
  119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 60 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 119 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 284 (accept_3_2 58 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 284 (Polychromatic418967fa.accept_13_4_2_11_1_733
  56 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 284 (accept_3_2 55
  119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 284
  (Polychromatic418967fa.accept_20_14_19_4_1_7534 54 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 284 (accept_3_2 52 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 284 (accept_3_2 49 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 284 (Polychromatic418967fa.accept_19_9_5_18_1_3891 47 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 284 (accept_3_2 46 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 119 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 284 (accept_3_2 43 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 284 (Polychromatic418967fa.accept_18_5_11_14_1_7203 41 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 284 (accept_3_2 40 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 284
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 284 (accept_3_2 37 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 284 (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 284 (accept_3_2 34 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 284
  (Polychromatic418967fa.accept_19_13_5_18_1_8106 32 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 119 284 (accept_3_2 31 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 119 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 284 (Polychromatic418967fa.accept_13_3_2_11_1_1999 29 119
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 284 (accept_3_2 28 119
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 119 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 284 (accept_3_2 25 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 119 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 284 (Polychromatic418967fa.accept_10_3_9_4_1_960
  23 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 284 (accept_3_2 22
  119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 119 284 (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 284 (accept_3_2 19 119 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 119 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 284 (accept_3_2 16 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 284 (accept_3_2 13 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 284 (accept_3_2 10 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 284 (accept_3_2 7 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 119 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 284
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 284 (accept_3_2 4 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 284 (accept_3_2 1 119 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 118 284 (allA_of_3_0 118 118 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 117 284
  (allA_succ_of_accept 116 117 284 (Polychromatic418967fa.accept_15_11_12_14_1_2612 116 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 117 284 (accept_3_2 115 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 114 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 117 284 (accept_3_2 112 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 117 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 111 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 117 284 (Polychromatic418967fa.accept_19_15_3_18_1_5241 110 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 284 (accept_3_2 109 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 284 (Polychromatic418967fa.accept_21_3_12_11_1_7034 108
  117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 117 284 (accept_3_2 106 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 117 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 105 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 117 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 104 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 284 (accept_3_2 103 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 102 117
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 117 284 (accept_3_2 100 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 117 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 99 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 117 284 (Polychromatic418967fa.accept_21_14_12_11_1_3956 98 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 284 (accept_3_2 97 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 284 (Polychromatic418967fa.accept_18_6_9_14_1_9915 96 117
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 284 (accept_3_2 94 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 117 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 117 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 92 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 117 284 (accept_3_2 91 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 117 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 117 284 (accept_3_2 88 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 117 284 (Polychromatic418967fa.accept_16_7_5_12_1_4824 87 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 117 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 117 284 (accept_3_2 85 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 84 117 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 117 284 (accept_3_2 82 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 117 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 117 284 (Polychromatic418967fa.accept_19_4_3_18_1_2699 80 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 284 (accept_3_2 79 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 117 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 284 (accept_3_2 76 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 117 284 (Polychromatic418967fa.accept_18_3_9_14_1_2219 75 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 117 284 (Polychromatic418967fa.accept_16_10_5_12_1_4925 74 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 284 (accept_3_2 73 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 117 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 284 (accept_3_2 70 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 117 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 117 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 68 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 284 (accept_3_2 67 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 117 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 117
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 284 (accept_3_2 64 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 117 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 284 (accept_3_2 61 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 284 (accept_3_2 58 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 117 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 117 284 (Polychromatic418967fa.accept_15_11_12_14_1_2612 56 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 284 (accept_3_2 55 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 117
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 284 (accept_3_2 52 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 117 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 117 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 284 (accept_3_2 49 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 284 (accept_3_2 46 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 284 (Polychromatic418967fa.accept_21_3_12_11_1_7034 45 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 284 (accept_3_2 43 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 284 (accept_3_2 40 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 38 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 284 (accept_3_2 37 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 117 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 284 (accept_3_2 34 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 284 (accept_3_2 31 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 117 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 284 (accept_3_2 28 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 284 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 284 (accept_3_2 25 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 117
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 284 (accept_3_2 22 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 284 (accept_3_2 19 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 284 (accept_3_2 16 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 284 (Polychromatic418967fa.accept_17_14_15_12_1_1921 14 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 284 (accept_3_2 13 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 117
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 284 (accept_3_2 10 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 284 (accept_3_2 7 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 117 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 284 (accept_3_2 4 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 117 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 284 (accept_3_2 1 117 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 284 (allA_succ_of_accept 115 116 284 (accept_3_2 115 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 116 284 2 57 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 116 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 113 116 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 116 284 4 28 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 116 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 111 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 116 284 2 55 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 116 284 (accept_3_2 109 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 116 284 4 27 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 116 284 (Polychromatic418967fa.accept_16_11_4_12_1_1760 107 116 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 116 284 2 53 58 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 116 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 105 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 116 284 4 26 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 116 284 (accept_3_2 103 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 116 284 2 51 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 116 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 101 116 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 116 284 4 25 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 116 284
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 99 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 116 284 2 49 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 116 284 (accept_3_2 97 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 116 284 4 24 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 116 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 95 116 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 116 284 2 47 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 116 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 93 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 116 284 4 23 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 116 284 (accept_3_2 91 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 116 284 2 45 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 116 284 (Polychromatic418967fa.accept_16_9_4_12_1_4896 89 116 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 116 284 4 22 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 116 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 87 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 116 284 2 43 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 116 284 (accept_3_2 85 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 116 284 4 21 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 116 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 116 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 116 284 2 41 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 116 284
  (Polychromatic418967fa.accept_16_1_4_12_1_376 81 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 116 284 4 20 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 284 (accept_3_2 79 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 116 284 2 39 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 116 284 (Polychromatic418967fa.accept_16_13_4_12_1_1805 77 116 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 116 284 4 19 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 116 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 116 284 2 37 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 116 284 (accept_3_2 73 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 116 284 4 18 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 116 284 (Polychromatic418967fa.accept_16_7_4_12_1_1806 71 116 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 116 284 2 35 58 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 116 284 4 17 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 116 284 (accept_3_2 67 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 116 284 2 33 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 116 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 116 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 284 4 16 29 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 284
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 116 284 2 31 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 116 284 (accept_3_2 61 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 284 4 15 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 284 (Polychromatic418967fa.accept_13_7_12_11_1_1911 59 116 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 284 2 29 58 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 284 4 14 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 284 (accept_3_2 55 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 284 2 27 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 284 (Polychromatic418967fa.accept_13_1_12_11_1_728 53 116 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 284 4 13 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 284 2 25 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 284 (accept_3_2 49 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 284 4 12 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 116 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 284 2 23 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 284 4 11 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 284 (accept_3_2 43 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 284 2 21 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 284 (Polychromatic418967fa.accept_16_9_4_12_1_4896 41 116 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 284 4 10 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 284 2 19 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 284 (accept_3_2 37 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 284 4 9 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 116 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 284 2 17 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 33
  116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 284 4 8 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 284 (accept_3_2 31
  116 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 284 2 15 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 284 4 7 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 284 (Polychromatic418967fa.accept_13_1_12_11_1_728 27 116 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 284 2 13 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 284 (accept_3_2 25 116 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 284 4 6 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 284 (Polychromatic418967fa.accept_13_10_12_11_1_731 23 116
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 284 2 11 58 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 284 4 5 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 284 (accept_3_2 19 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 284 2 9 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 284 (Polychromatic418967fa.accept_13_4_12_11_1_5362 17 116 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 284 4 4 29 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 284 2 7 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 116 284 (accept_3_2 13 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 116 284 4 3 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 116 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 284 2 5 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 284 (Polychromatic418967fa.accept_16_9_4_12_1_4896
  9 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 284 4 2 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 284 (accept_3_2 7
  116 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 284 2 3 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 116 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 116 284 4 1 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 116 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 116 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 284 2 1 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 284 (accept_3_2 1 116 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 115 284 (allA_of_3_0 115 115 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 114 284
  (allA_succ_of_accept 113 114 284 (Polychromatic418967fa.accept_15_8_9_14_1_4577 113 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 114 284 2 56 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 114 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 111 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 114 284 2 55 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 114 284 (accept_3_2 109 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 114 284 2 54 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 114 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 107 114 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 114 284 2 53 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 114 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 105 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 114 284 2 52 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 114 284 (accept_3_2 103 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 114 284 2 51 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 114 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 101 114 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 114 284 2 50 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 114 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 99 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 114 284 2 49 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 114 284 (accept_3_2 97 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 114 284 2 48 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 114 284 (Polychromatic418967fa.accept_13_4_10_11_1_1908 95 114 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 114 284 2 47 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 114 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 93 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 114 284 2 46 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 114 284 (accept_3_2 91 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 284 2 45 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 114 284 2 44 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 114 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 114 284 2 43 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 114 284 (accept_3_2 85 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 284 2 42 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 284 2 41 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 114 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 114 284 2 40 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 114 284 (accept_3_2 79 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 284 2 39 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 284 (Polychromatic418967fa.accept_13_12_10_11_1_1279 77 114 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 284 2 38 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 114 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 114 284 2 37 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 114 284 (accept_3_2 73 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 284 2 36 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 284 2 35 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 114 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 114 284 2 34 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 114 284 (accept_3_2 67 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 284 2 33 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 284 2 32 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 114 284 2 31 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 114 284 (accept_3_2 61 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 284 2 30 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 284 (Polychromatic418967fa.accept_20_19_14_4_1_7634 59 114 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 284 2 29 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 114 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 114 284 2 28 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 114 284 (accept_3_2 55 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 284 2 27 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 284 2 26 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 114 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 114 284 2 25 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 114 284 (accept_3_2 49 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 284 2 24 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 284 2 23 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 284 2 22 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 284 (accept_3_2 43 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 284 2 21 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 284 2 20 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 284 2 19 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 284 (accept_3_2 37 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 284 2 18 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 284 2 17 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 284 2 16 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 284 (accept_3_2 31 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 284 2 15 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 284 2 14 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 284 2 13 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 284 (accept_3_2 25 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 284 2 12 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 114 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 284 2 11 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 284 2 10 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 284 (accept_3_2 19 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 284 2 9 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 284 2 8 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 284 2 7 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 114 284 (accept_3_2 13 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 284 2 6 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 114 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 284 2 5 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 284 2 4 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 284 (accept_3_2 7 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114
  284 2 3 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  114 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 114 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 284 2 2 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 114 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 114 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 284 2 1 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 284 (accept_3_2 1 114 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 284 (allA_succ_of_accept 112 113 284 (accept_3_2 112 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 113 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 110 113
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 113 284 (accept_3_2 109 113
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 113 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 108 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 113 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 107 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 113 284 (accept_3_2 106 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 113 284
  (Polychromatic418967fa.accept_16_8_1_12_1_984 104 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 113 284 (accept_3_2 103 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 113 284 (Polychromatic418967fa.accept_21_18_8_11_1_10083 102 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 101 113 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 101 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 113 284 (accept_3_2 100 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 113 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 113 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 98 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 113 284 (accept_3_2 97 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 113 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 113 284 (Polychromatic418967fa.accept_14_11_1_4_1_4445 95 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 113 284 (accept_3_2 94 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 113 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 113 284
  (Polychromatic418967fa.accept_13_1_9_11_1_703 92 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 113 284 (accept_3_2 91 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 113 284 (Polychromatic418967fa.accept_22_2_3_20_1_4812 90 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 113 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 113 284 (accept_3_2 88 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 113 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 113 284 (accept_3_2 85 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 113 284 (Polychromatic418967fa.accept_15_9_8_14_1_1699 84 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 113 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 83 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 284 (accept_3_2 82 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 113 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 284 (accept_3_2 79 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 284 (Polychromatic418967fa.accept_29_20_26_23_1_17399 78 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 284 (accept_3_2 76 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 113 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 284 (accept_3_2 73 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 284 (Polychromatic418967fa.accept_20_11_13_4_1_7573 71 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 284 (accept_3_2 70 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 113 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 284 (accept_3_2 67 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 65 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 284 (accept_3_2 64 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 113 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 284 (accept_3_2 61 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 284 (Polychromatic418967fa.accept_13_8_9_11_1_1265 60 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 284 (accept_3_2 58 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 284
  (Polychromatic418967fa.accept_16_8_1_12_1_984 56 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 284 (accept_3_2 55 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 284 (accept_3_2 52 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 284
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 284 (accept_3_2 49 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 284 (Polychromatic418967fa.accept_17_14_11_12_1_4109 48 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 284 (accept_3_2 46 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 284
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 44 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 284 (accept_3_2 43 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 284 (Polychromatic418967fa.accept_23_19_21_8_1_14212 42 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 284 (Polychromatic418967fa.accept_13_2_9_11_1_258 41 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 284 (accept_3_2 40 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 284 (accept_3_2 37 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 284 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 284 (accept_3_2 34 113 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 284
  (Polychromatic418967fa.accept_22_10_3_20_1_4878 32 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 113 284 (accept_3_2 31 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 113 284 (Polychromatic418967fa.accept_17_13_11_12_1_4131 30 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 284 (Polychromatic418967fa.accept_8_5_1_4_1_628
  29 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 284 (accept_3_2 28
  113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 113 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 284 (accept_3_2 25 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 113 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 284
  (Polychromatic418967fa.accept_17_6_11_12_1_4107 23 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 113 284 (accept_3_2 22 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 284 (Polychromatic418967fa.accept_13_7_9_11_1_705 20 113
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 284 (accept_3_2 19 113
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 284
  (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 113 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 284 (accept_3_2 16 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 284 (Polychromatic418967fa.accept_12_2_5_8_1_159
  14 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 284 (accept_3_2 13
  113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 113 284 (Polychromatic418967fa.accept_14_11_1_4_1_4445 11 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 284 (accept_3_2 10 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 284 (Polychromatic418967fa.accept_13_8_9_11_1_1265
  8 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 284 (accept_3_2 7
  113 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 284
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 113 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 284 (accept_3_2 4 113 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 113 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  113 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 284 (accept_3_2 1 113
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 112 284 (allA_of_3_0 112 112 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 111 284
  (allA_succ_of_accept 110 111 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 110 111 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 111 284 (accept_3_2 109 111 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 111 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 108 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 111 284 (accept_3_2 106 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 111 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 111 284 (Polychromatic418967fa.accept_16_8_15_12_1_1747 104 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 111 284 (accept_3_2 103 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 102 111
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 111 284 (accept_3_2 100 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 111 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 99 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 111 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 98 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 284 (accept_3_2 97 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 111 284 (accept_3_2 94 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 111 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 111 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 92 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 284 (accept_3_2 91 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 111 284 (accept_3_2 88 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 111 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 111 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 284 (accept_3_2 85 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627 84 111 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 284 (accept_3_2 82 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 111 284 (Polychromatic418967fa.accept_13_3_7_11_1_1904 81 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 111 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 284 (accept_3_2 79 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 111 284 (accept_3_2 76 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 111 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 111 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 284 (accept_3_2 73 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 284 (accept_3_2 70 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 111 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 111 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 284 (accept_3_2 67 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 284 (accept_3_2 64 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 111 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 63 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 111 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 284 (accept_3_2 61 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 284 (accept_3_2 58 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 111 284 (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 111 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 284 (accept_3_2 55 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 284 (accept_3_2 52 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 111 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 111 284 (Polychromatic418967fa.accept_15_5_6_14_1_1721 50 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 284 (accept_3_2 49 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 284 (Polychromatic418967fa.accept_13_9_7_11_1_1292 48 111
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 284 (accept_3_2 46 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 284 (accept_3_2 43 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 284 (accept_3_2 40 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 284 (accept_3_2 37 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 284 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 111 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 284 (accept_3_2 34 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 284 (accept_3_2 31 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 111 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 284 (accept_3_2 28 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 284 (accept_3_2 25 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 284 (accept_3_2 22 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 284 (accept_3_2 19 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 284 (accept_3_2 16 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 284 (Polychromatic418967fa.accept_13_1_7_11_1_702 14 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 284 (accept_3_2 13 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 284 (accept_3_2 10 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 284 (accept_3_2 7 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 284 (accept_3_2 4 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 284 (accept_3_2 1 111 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 284 (allA_succ_of_accept 109 110 284 (accept_3_2 109 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 110 284 2 54 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 110 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 107 110 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 110 284 2 53 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 110 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 105 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 110 284 2 52 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 110 284 (accept_3_2 103 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 110 284 2 51 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 110 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 101 110 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 110 284 2 50 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 110 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 99 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 110 284 2 49 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 110 284 (accept_3_2 97 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 110 284 2 48 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 110 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 110 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 110 284 2 47 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 110 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 93 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 110 284 2 46 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 110 284 (accept_3_2 91 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 110 284 2 45 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 110 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 110 284 2 44 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 110 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 87 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 110 284 2 43 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 110 284 (accept_3_2 85 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 110 284 2 42 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 110 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 110 284 2 41 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 110 284
  (Polychromatic418967fa.accept_15_6_5_14_1_429 81 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 110 284 2 40 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 110 284 (accept_3_2 79 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 110 284 2 39 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 110 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 110 284 2 38 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 75 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 284 2 37 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 284 (accept_3_2 73 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 284 2 36 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 284 2 35 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 284 2 34 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 284 (accept_3_2 67 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 284 2 33 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 110 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 284 2 32 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 284
  (Polychromatic418967fa.accept_25_13_10_9_1_8706 63 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 110 284 2 31 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 110 284 (accept_3_2 61 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 284 2 30 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 110 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 284 2 29 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 284 2 28 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 284 (accept_3_2 55 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 284 2 27 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 284 2 26 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 284 2 25 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 284 (accept_3_2 49 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 284 2 24 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 110 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 284 2 23 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 284
  (Polychromatic418967fa.accept_19_7_15_18_1_8132 45 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 110 284 2 22 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 110 284 (accept_3_2 43 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 284 2 21 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 284 2 20 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 284 2 19 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 284 (accept_3_2 37 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 284 2 18 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 284 2 17 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 284 2 16 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 284 (accept_3_2 31 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 284 2 15 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 284 2 14 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 284 2 13 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 284 (accept_3_2 25 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 284 2 12 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 284 2 11 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 284 2 10 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 284 (accept_3_2 19 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 284 2 9 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 110 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 110 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 284 2 8 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 110 284 2 7 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 110 284 (accept_3_2 13 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 110 284 2 6 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 110 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 110 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 284 2 5 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 284 2 4 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 284 (accept_3_2 7 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  284 2 3 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 110 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 284 2 2 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 110 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 284 2 1 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 284 (accept_3_2 1 110 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 109 284 (allA_of_3_0 109 109 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 108 284
  (allA_succ_of_accept 107 108 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 107 108 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 108 284 2 53 54 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 108 284
  (Polychromatic418967fa.accept_14_7_10_4_1_130 105 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 108 284 4 26 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 108 284 (accept_3_2 103 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 108 284 2 51 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 108 284 (Polychromatic418967fa.accept_13_10_4_11_1_1969 101 108 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 108 284 4 25 27 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 108 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 99 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 108 284 2 49 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 108 284 (accept_3_2 97 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 284 4 24 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 284 (Polychromatic418967fa.accept_17_10_6_12_1_11635 95 108 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 108 284 2 47 54 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 108 284
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 93 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 108 284 4 23 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 108 284 (accept_3_2 91 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 108 284 2 45 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 108 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 89 108 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 284 4 22 27 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 108 284
  (Polychromatic418967fa.accept_17_2_6_12_1_7912 87 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 108 284 2 43 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 108 284 (accept_3_2 85 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 284 4 21 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 108 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 284 2 41 54 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 108 284
  (Polychromatic418967fa.accept_19_5_13_18_1_5249 81 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 108 284 4 20 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 108 284 (accept_3_2 79 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 284 2 39 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 284 (Polychromatic418967fa.accept_13_12_4_11_1_1925 77 108 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 284 4 19 27 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 108 284
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 75 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 108 284 2 37 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 108 284 (accept_3_2 73 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 284 4 18 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 108 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 284 2 35 54 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 108 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 108 284 4 17 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 108 284 (accept_3_2 67 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 284 2 33 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 284 (Polychromatic418967fa.accept_19_8_13_18_1_8130 65 108 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 284 4 16 27 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 108 284
  (Polychromatic418967fa.accept_14_7_10_4_1_130 63 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 108 284 2 31 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 108 284 (accept_3_2 61 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 284 4 15 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 108 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 284 2 29 54 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 108 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 108 284 4 14 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 284 (accept_3_2 55 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 284 2 27 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 284 (Polychromatic418967fa.accept_17_2_6_12_1_7912 53 108 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 284 4 13 27 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 108 284
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 51 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 108 284 2 25 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 108 284 (accept_3_2 49 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 284 4 12 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 284 (Polychromatic418967fa.accept_13_8_4_11_1_3469 47 108 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 284 2 23 54 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 108 284
  (Polychromatic418967fa.accept_13_6_4_11_1_282 45 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 108 284 4 11 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 108 284 (accept_3_2 43 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 284 2 21 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 108 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 284 4 10 27 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 108 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 108 284 2 19 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 108 284 (accept_3_2 37 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 284 4 9 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 284 (Polychromatic418967fa.accept_14_7_10_4_1_130 35 108 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 284 2 17 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 284 (Polychromatic418967fa.accept_13_7_4_11_1_1967
  33 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 284 4 8 27 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 284
  (accept_3_2 31 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 284 2 15 54 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 284 4 7 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 284 2 13 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 284 (accept_3_2 25 108 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 284 4 6 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 284 (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 108
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 284 2 11 54 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 284
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 284 4 5 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 108 284 (accept_3_2 19 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  108 284 2 9 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 108 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 284 4 4 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 284 2 7 54 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 284 (accept_3_2 13
  108 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 284 4 3 27 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 284
  (Polychromatic418967fa.accept_15_11_3_14_1_971 11 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 284 2 5 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 108 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 108 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 284 4 2 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 284 (accept_3_2 7 108 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 284 2 3 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 284 (Polychromatic418967fa.accept_19_5_13_18_1_5249 5 108
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 284 4 1 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 284
  (Polychromatic418967fa.accept_23_3_16_8_1_12679 3 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 284 2 1 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 284 (accept_3_2 1 108 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 284 (allA_succ_of_accept 106 107 284 (accept_3_2 106 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 107 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 107 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 104 107
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 107 284 (accept_3_2 103 107
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 107 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 102 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 107 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 101 107 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 107 284 (accept_3_2 100 107 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 107 284 (Polychromatic418967fa.accept_11_10_8_9_1_492
  98 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 107 284 (accept_3_2 97
  107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 107 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 96 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 107 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 95 107 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 107 284 (accept_3_2 94 107 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 107 284 (Polychromatic418967fa.accept_9_2_8_5_1_228
  92 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 107 284 (accept_3_2 91
  107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 107 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 90 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 107 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 107 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 284 (accept_3_2 88 107 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 284 (Polychromatic418967fa.accept_12_2_11_8_1_504
  86 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 284 (accept_3_2 85
  107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 107 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 84 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 107 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 107 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 284 (accept_3_2 82 107 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 284
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 80 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 284 (accept_3_2 79 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 284 (Polychromatic418967fa.accept_17_9_5_12_1_6606 77 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 284 (accept_3_2 76 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 107 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 284 (accept_3_2 73 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 284 (accept_3_2 70 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 284 (accept_3_2 67 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 284 (accept_3_2 64 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 284 (accept_3_2 61 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 284 (Polychromatic418967fa.accept_13_7_3_11_1_280 59 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 284 (accept_3_2 58 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 284 (accept_3_2 55 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 53 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 284 (accept_3_2 52 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 284 (accept_3_2 49 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 284 (accept_3_2 46 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 284
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 44 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 284 (accept_3_2 43 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 284 (accept_3_2 40 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 284 (accept_3_2 37 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 284 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 284 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 284 (accept_3_2 34 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 284 (accept_3_2 31 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 284 (accept_3_2 28 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 284 (accept_3_2 25 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 284 (accept_3_2 22 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 284 (accept_3_2 19 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 284 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 284 (Polychromatic418967fa.accept_16_1_11_12_1_1774 17 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 284 (accept_3_2 16 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 284 (accept_3_2 13 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 284 (accept_3_2 10 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 284
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 8 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 284 (accept_3_2 7 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 284 (accept_3_2 4 107 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 284 (accept_3_2 1 107 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 106 284 (allA_of_3_0 106 106 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 105 284
  (allA_succ_of_accept 104 105 284 (Polychromatic418967fa.accept_16_8_9_12_1_1737 104 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 105 284 (accept_3_2 103 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 105 284 (accept_3_2 100 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 105 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 99 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 105 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 105 284 (accept_3_2 97 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 96 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 105 284 (accept_3_2 94 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 105 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 93 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 105 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 284 (accept_3_2 91 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 105 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 105 284 (accept_3_2 88 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 105 284 (Polychromatic418967fa.accept_13_9_1_11_1_275 87 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 105 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 86 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 284 (accept_3_2 85 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 105 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 284 (accept_3_2 82 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 105 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 81 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 105 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 284 (accept_3_2 79 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 105 284 (accept_3_2 76 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 105 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 284 (accept_3_2 73 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 284 (Polychromatic418967fa.accept_13_7_1_11_1_732 72 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 284 (accept_3_2 70 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 105 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 284 (Polychromatic418967fa.accept_13_3_1_11_1_1268 68 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 284 (accept_3_2 67 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 105 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 284 (accept_3_2 64 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 284 (Polychromatic418967fa.accept_22_19_17_20_1_14411 63 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 284 (accept_3_2 61 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 284 (Polychromatic418967fa.accept_13_8_1_11_1_1284 60 105
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 284 (accept_3_2 58 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 284 (accept_3_2 55 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 284 (accept_3_2 52 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 284 (Polychromatic418967fa.accept_16_2_9_12_1_46 50 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 284 (accept_3_2 49 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 105 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 284 (accept_3_2 46 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 284 (accept_3_2 43 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 284 (accept_3_2 40 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 284 (accept_3_2 37 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 284 (accept_3_2 34 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 284 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 284 (Polychromatic418967fa.accept_17_15_3_12_1_9179 32 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 284 (accept_3_2 31 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 105 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 284 (accept_3_2 28 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 284 (Polychromatic418967fa.accept_19_8_10_18_1_5232 27 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 284 (accept_3_2 25 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 284 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 105 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 284 (accept_3_2 22 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 284 (accept_3_2 19 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 284 (accept_3_2 16 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 284 (Polychromatic418967fa.accept_17_15_3_12_1_9179 15 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 284 (accept_3_2 13 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 284 (accept_3_2 10 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 284 (accept_3_2 7 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 105 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 284 (accept_3_2 4 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 284 (accept_3_2 1 105 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 284 (allA_succ_of_accept 103 104 284 (accept_3_2 103 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 104 284 2 51 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 104 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 101 104 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 104 284 4 25 26 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 104 284
  (Polychromatic418967fa.accept_16_3_8_12_1_2736 99 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 104 284 2 49 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 104 284 (accept_3_2 97 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 104 284 4 24 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 104 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 95 104 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 104 284 2 47 52 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 93 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 104 284 4 23 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 104 284 (accept_3_2 91 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 104 284 2 45 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 104 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 89 104 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 104 284 4 22 26 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 87 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 104 284 2 43 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 104 284 (accept_3_2 85 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 104 284 4 21 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 104 284 (Polychromatic418967fa.accept_16_3_8_12_1_2736 83 104 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 284 2 41 52 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 284
  (Polychromatic418967fa.accept_16_1_8_12_1_405 81 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 284 4 20 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 284 (accept_3_2 79 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 284 2 39 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 284 (Polychromatic418967fa.accept_16_13_8_12_1_2723 77 104 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 284 4 19 26 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 284 2 37 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 284 (accept_3_2 73 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 284 4 18 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 284 (Polychromatic418967fa.accept_16_7_8_12_1_4902 71 104 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 284 2 35 52 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 284
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 69 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 284 4 17 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 284 (accept_3_2 67 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 284 2 33 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 104 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 284 4 16 26 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 284
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 104 284 2 31 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 104 284 (accept_3_2 61 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 284 4 15 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 104 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 284 2 29 52 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 284
  (Polychromatic418967fa.accept_16_9_8_12_1_979 57 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 284 4 14 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 284 (accept_3_2 55 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 284 2 27 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 284 (Polychromatic418967fa.accept_16_5_8_12_1_1766 53 104 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 284 4 13 26 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 284 2 25 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 284 (accept_3_2 49 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 284 4 12 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 104 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 284 2 23 52 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 284 4 11 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 284 (accept_3_2 43 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 284 2 21 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 284 (Polychromatic418967fa.accept_16_9_8_12_1_979 41 104 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 284 4 10 26 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 284
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 39 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 284 2 19 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 284 (accept_3_2 37 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 284 4 9 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 284 (Polychromatic418967fa.accept_16_3_8_12_1_2736 35 104 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 284 2 17 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 284 4 8 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 284 (accept_3_2 31
  104 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 284 2 15 52 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 284
  (Polychromatic418967fa.accept_11_7_5_9_1_884 29 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 104 284 4 7 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 284 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 104 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 284 2 13 52 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 284 (accept_3_2 25 104 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 284 4 6 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23
  104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 284 2 11 52 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 284
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 284 4 5 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 284 (accept_3_2 19 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 284 2 9 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 104 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 284 4 4 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 284
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 104 284 2 7 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 104 284 (accept_3_2 13 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 104 284 4 3 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 104 284 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 104 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 284 2 5 52 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 284 4 2 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 284 (accept_3_2 7 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  284 2 3 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 104 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 284 4 1 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 104 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 104 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 284 2 1 52 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 284 (accept_3_2 1 104 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 104
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  103 284 (allA_of_3_0 103 103 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 102 284 (allA_succ_of_accept 101
  102 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 101 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 102 284 2 50 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 102 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 102 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 284 2 49 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 284 (accept_3_2 97 102 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 102 284 2 48 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 284
  (Polychromatic418967fa.accept_20_15_2_4_1_11882 95 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 94 102 284 2 47 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 93 102 284 (Polychromatic418967fa.accept_12_9_6_8_1_518 93 102 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 284 2 46 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 284 (accept_3_2 91 102 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 102 284 2 45 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 89 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 102 284 2 44 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 102 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 284 2 43 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 284 (accept_3_2 85 102 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 102 284 2 42 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 102 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 83
  102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 284 2 41 51 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 102 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 102 284 2 40 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 102 284 (accept_3_2 79 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 284 2 39 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 284 2 38 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 102 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 102 284 2 37 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 102 284 (accept_3_2 73 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 284 2 36 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 284 2 35 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 102 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 102 284 2 34 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 102 284 (accept_3_2 67 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 284 2 33 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 284 2 32 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 102 284 2 31 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 284 (accept_3_2 61 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 284 2 30 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 284 (Polychromatic418967fa.accept_20_19_2_4_1_2057 59 102 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 284 2 29 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 284 2 28 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 284 (accept_3_2 55 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 284 2 27 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 284 2 26 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 284 2 25 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 284 (accept_3_2 49 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 284 2 24 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 284 2 23 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 284 2 22 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 284 (accept_3_2 43 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 284 2 21 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 284 (Polychromatic418967fa.accept_15_11_12_14_1_2612 41 102 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 284 2 20 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 284
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 284 2 19 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 284 (accept_3_2 37 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 284 2 18 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 284 2 17 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 284 2 16 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 284 (accept_3_2 31 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 284 2 15 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 284 2 14 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 284 2 13 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 284 (accept_3_2 25 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 284 2 12 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 284 (Polychromatic418967fa.accept_22_1_14_20_1_9826 23 102 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 284 2 11 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 284 2 10 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 284 (accept_3_2 19 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 284 2 9 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 284 2 8 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 102 284 2 7 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 102 284 (accept_3_2 13 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 284 2 6 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 284 2 5 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 284 2 4 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 284 (accept_3_2 7 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102
  284 2 3 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  102 284 (Polychromatic418967fa.accept_20_5_2_4_1_7655 5 102 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 284 2 2 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 102 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 102 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 284 2 1 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 284 (accept_3_2 1 102 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 284 (allA_succ_of_accept 100 101 284 (accept_3_2 100 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 101 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 101 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 101 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 101 284 (accept_3_2 97 101 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 284 (Polychromatic418967fa.accept_9_6_2_5_1_506
  96 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 284
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 95 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 284 (accept_3_2 94 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 92 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 284 (accept_3_2 91 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 89 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 284 (accept_3_2 88 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 86 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 284 (accept_3_2 85 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 101 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 83 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 284 (accept_3_2 82 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 284 (accept_3_2 79 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 284
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 77 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 284 (accept_3_2 76 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 284 (accept_3_2 73 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 284 (Polychromatic418967fa.accept_15_12_11_14_1_3464 72
  101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 284 (accept_3_2 70 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 284 (Polychromatic418967fa.accept_13_3_10_11_1_1293 68 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 284 (accept_3_2 67 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 101 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 284 (accept_3_2 64 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 284 (accept_3_2 61 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 284
  (Polychromatic418967fa.accept_11_4_2_9_1_496 59 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 284 (accept_3_2 58 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 284 (Polychromatic418967fa.accept_13_4_10_11_1_1908 56 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 284 (accept_3_2 55 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 284 (Polychromatic418967fa.accept_13_2_10_11_1_1276 54 101
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 284 (accept_3_2 52 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 284 (accept_3_2 49 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 284
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 284 (accept_3_2 46 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 284 (accept_3_2 43 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 284 (accept_3_2 40 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 284 (accept_3_2 37 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 101 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 284 (accept_3_2 34 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 284 (Polychromatic418967fa.accept_27_5_20_14_1_17398 32 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 284 (accept_3_2 31 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 101 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 284 (accept_3_2 28 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 284 (accept_3_2 25 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 284
  (Polychromatic418967fa.accept_16_7_5_12_1_4824 23 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 284 (accept_3_2 22 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 284 (accept_3_2 19 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 284 (accept_3_2 16 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 284 (accept_3_2 13 101 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 101 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 284
  (Polychromatic418967fa.accept_17_11_16_12_1_1984 11 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 284 (accept_3_2 10 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 101 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 284 (accept_3_2 7 101 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 284
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 284 (accept_3_2 4 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 284 (accept_3_2 1 101 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  100 284 (allA_of_3_0 100 100 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 99 284 (allA_succ_of_accept 98 99
  284 (Polychromatic418967fa.accept_10_8_9_4_1_961 98 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 99 284 (accept_3_2 97 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 99 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 99 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 99 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 284 (accept_3_2 94 99 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 284 (Polychromatic418967fa.accept_10_3_9_4_1_960
  93 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 99 284
  (Polychromatic418967fa.accept_13_1_8_11_1_724 92 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 284 (accept_3_2 91 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  99 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 284 (accept_3_2 88 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 99 284
  (Polychromatic418967fa.accept_27_5_18_14_1_5921 86 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 284 (accept_3_2 85 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  99 284 (Polychromatic418967fa.accept_13_6_8_11_1_5398 84 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 284 (accept_3_2 82 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 284 (Polychromatic418967fa.accept_13_3_8_11_1_1906 81 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 99 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 284 (accept_3_2 79 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  99 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 78 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 284 (accept_3_2 76 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 284
  (Polychromatic418967fa.accept_13_9_8_11_1_725 74 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 284 (accept_3_2 73 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  99 284 (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 284 (accept_3_2 70 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 284 (Polychromatic418967fa.accept_13_4_8_11_1_1937 69 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 99 284 (accept_3_2 67 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  99 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 284 (accept_3_2 64 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 284
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 62 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 284 (accept_3_2 61 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 284 (Polychromatic418967fa.accept_17_9_14_12_1_9177 60 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 284 (accept_3_2 58 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 284 (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 284
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 56 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 284 (accept_3_2 55 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 284 (accept_3_2 52 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 284 (Polychromatic418967fa.accept_15_6_9_14_1_3457 51 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 284
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 50 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 284 (accept_3_2 49 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 284 (accept_3_2 46 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 284
  (Polychromatic418967fa.accept_25_19_24_9_1_17397 44 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 99 284 (accept_3_2 43 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 99 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 284 (accept_3_2 40 99 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 39
  99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 284 (accept_3_2 37 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 284 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 284 (accept_3_2 34 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 284
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 32 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 284 (accept_3_2 31 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 284 (accept_3_2 28 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 284 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 284 (accept_3_2 25 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 284 (accept_3_2 22 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 284 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 284
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 284 (accept_3_2 19 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 284 (accept_3_2 16 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 284
  (Polychromatic418967fa.accept_13_1_8_11_1_724 14 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 284 (accept_3_2 13 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 284 (accept_3_2 10 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 284 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 99 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 284
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 284 (accept_3_2 7 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  284 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 284 (accept_3_2 4 99 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 99 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 284 (Polychromatic418967fa.accept_19_2_4_18_1_9556
  2 99 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 284 (accept_3_2 1 99
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  284 (allA_succ_of_accept 97 98 284 (accept_3_2 97 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96
  98 284 2 48 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 98 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 98 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 98 284 2 47 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 98 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 93
  98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 98 284 2 46 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 98 284 (accept_3_2 91
  98 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 98 284 2 45 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 98 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 89 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 98 284 2 44 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 98 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 98 284 2 43 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 98 284 (accept_3_2 85 98 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 284 2 42 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 83
  98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 98 284 2 41 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 98 284
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 81 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 98 284 2 40 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 98 284 (accept_3_2 79 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 98 284 2 39 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 98 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 98 284 2 38 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 98 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 98 284 2 37 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 98 284 (accept_3_2 73 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 98 284 2 36 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 98 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 284 2 35 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 98 284 2 34 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 98 284 (accept_3_2 67 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 98 284 2 33 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 98 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 284 2 32 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 284
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 98 284 2 31 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 98 284 (accept_3_2 61 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 284 2 30 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 98 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 284 2 29 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 98 284 2 28 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 284 (accept_3_2 55 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 98 284 2 27 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 98 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 98 284 2 26 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 98 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 98 284 2 25 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 98 284 (accept_3_2 49 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 98 284 2 24 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 98 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 284 2 23 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 284
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 284 2 22 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 98 284 (accept_3_2 43 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 98 284 2 21 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 284 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 284 2 20 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 284 2 19 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 98 284 (accept_3_2 37 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 98 284 2 18 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 98 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 284 2 17 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 284 2 16 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 98 284 (accept_3_2 31 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 284 2 15 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 98 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 284 2 14 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 284
  (Polychromatic418967fa.accept_13_1_7_11_1_702 27 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 284 2 13 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 98 284 (accept_3_2 25 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 98 284 2 12 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 98 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 98 284 2 11 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 98 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 98 284 2 10 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 98 284 (accept_3_2 19 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 98 284 2 9 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 98 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 284 2 8 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 284 2 7 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 284 (accept_3_2 13
  98 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 284 2 6 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 98 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 98 284 2 5 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 98 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 98 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 284 2 4 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 284 (accept_3_2 7 98 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 98 284 2 3 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 98 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 98 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 284 2 2 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 98
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 284 2 1 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 284 (accept_3_2 1 98
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  284 (allA_of_3_0 97 97 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 96 284 (allA_succ_of_accept 95 96 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 95 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 96 284 2 47 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 96 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 93 96 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 96 284 4 23 24 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 96 284 (accept_3_2 91 96 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 284 2 45 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 89
  96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 284 4 22 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 284
  (Polychromatic418967fa.accept_11_10_8_9_1_492 87 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 284 2 43 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 284 (accept_3_2 85 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 284 4 21 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 96 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 284 2 41 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 284 (Polychromatic418967fa.accept_13_3_5_11_1_716
  81 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 284 4 20 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 284 (accept_3_2 79
  96 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 284 2 39 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 284
  (Polychromatic418967fa.accept_21_14_12_11_1_3956 77 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 96 284 4 19 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 96 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 96 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 284 2 37 48 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 284 (accept_3_2 73 96 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 284 4 18 24 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 96 284 2 35 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 96 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 96 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 96 284 4 17 24 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 284 (accept_3_2 67 96 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 284 2 33 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 65
  96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 284 4 16 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 96 284
  (Polychromatic418967fa.accept_18_9_6_14_1_5913 63 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 96 284 2 31 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 96 284 (accept_3_2 61 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 284 4 15 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 284 (Polychromatic418967fa.accept_13_7_5_11_1_1927 59 96 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 284 2 29 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 57
  96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 284 4 14 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 284 (accept_3_2 55
  96 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 284 2 27 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 96 284 4 13 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 96 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 96 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 284 2 25 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 284 (accept_3_2 49 96 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 284 4 12 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 284 2 23 48 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 284 4 11 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 284 (accept_3_2 43 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96
  284 2 21 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 96 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 96 284 4 10 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 96 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 96 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 284 2 19 48 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 284 (accept_3_2 37 96 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 284 4 9 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35
  96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 284 2 17 48 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 284
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 284 4 8 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 284 (accept_3_2 31 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  284 2 15 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 96 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 284 4 7 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 284 2 13 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 284 (accept_3_2 25 96 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 284 4 6 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 284 2 11 48 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 284 4 5 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 284 (accept_3_2 19 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  284 2 9 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 284 4 4 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 284 2 7 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 284 (accept_3_2 13 96 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 284 4 3 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 96 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 284 2 5 48 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 284 4 2 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 284 (accept_3_2 7 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 284
  2 3 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  284 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 96 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 284 4 1 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 284 2 1 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 284 (accept_3_2 1 96 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 284
  (allA_succ_of_accept 94 95 284 (accept_3_2 94 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 92 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 284 (accept_3_2 91 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 90 95 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 284
  (Polychromatic418967fa.accept_10_9_5_4_1_966 89 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 284 (accept_3_2 88 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 86 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 284 (accept_3_2 85 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 284 (Polychromatic418967fa.accept_13_6_4_11_1_282 84 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 83 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 284 (accept_3_2 82 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 284 (Polychromatic418967fa.accept_13_2_4_11_1_2003 80 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 284 (accept_3_2 79 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 78 95
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 284
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 77 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 284 (accept_3_2 76 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 284 (accept_3_2 73 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 284 (Polychromatic418967fa.accept_13_7_4_11_1_1967 72 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 284
  (Polychromatic418967fa.accept_10_1_5_4_1_276 71 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 284 (accept_3_2 70 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 68 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 284 (accept_3_2 67 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 284
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 65 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 284 (accept_3_2 64 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 284 (accept_3_2 61 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 284 (accept_3_2 58 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 284 (accept_3_2 55 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 284 (Polychromatic418967fa.accept_13_2_4_11_1_2003 54 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 284
  (Polychromatic418967fa.accept_15_8_5_14_1_986 53 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 284 (accept_3_2 52 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 284 (accept_3_2 49 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 284 (Polychromatic418967fa.accept_25_23_20_9_1_14000 48 95 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 284
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 47 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 284 (accept_3_2 46 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 284 (Polychromatic418967fa.accept_18_8_5_14_1_3353 44 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 284 (accept_3_2 43 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 284 (Polychromatic418967fa.accept_17_8_10_12_1_5335 42 95
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 284
  (Polychromatic418967fa.accept_10_1_5_4_1_276 41 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 284 (accept_3_2 40 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 38 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 284 (accept_3_2 37 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 284 (accept_3_2 34 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 284 (Polychromatic418967fa.accept_13_6_4_11_1_282 32 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 284 (accept_3_2 31 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 284 (Polychromatic418967fa.accept_20_10_15_4_1_7525 30 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 284
  (Polychromatic418967fa.accept_10_9_5_4_1_966 29 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 284 (accept_3_2 28 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 284 (accept_3_2 25 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 284
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 284 (accept_3_2 22 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 284 (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 284 (accept_3_2 19 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 284 (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 95
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 284
  (Polychromatic418967fa.accept_15_2_5_14_1_61 17 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 284 (accept_3_2 16 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 284 (accept_3_2 13 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 284 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 284 (accept_3_2 10 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 284 (Polychromatic418967fa.accept_13_8_4_11_1_3469 8 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 284 (accept_3_2 7 95 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 95 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 284
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 284 (accept_3_2 4 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 95 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 284 (accept_3_2 1 95 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 284
  (allA_of_3_0 94 94 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 93 284 (allA_succ_of_accept 92 93 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 92 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 93 284 (accept_3_2 91 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  93 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 284 (accept_3_2 88 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 93 284
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 86 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 284 (accept_3_2 85 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  93 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 84 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 284 (accept_3_2 82 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 81 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 80 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 284 (accept_3_2 79 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  93 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 284 (accept_3_2 76 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 93 284 (accept_3_2 73 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  93 284 (Polychromatic418967fa.accept_14_2_9_4_1_1735 72 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 284 (accept_3_2 70 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 284 (accept_3_2 67 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  93 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 284 (accept_3_2 64 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 284 (Polychromatic418967fa.accept_16_15_13_12_1_1787 63 93 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 284 (accept_3_2 61 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  93 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 284 (accept_3_2 58 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 93 284 (accept_3_2 55 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  93 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 284 (accept_3_2 52 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 284
  (Polychromatic418967fa.accept_19_12_17_18_1_14776 50 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 93 284 (accept_3_2 49 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 93 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 93 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 284 (accept_3_2 46 93 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361
  45 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 284 (accept_3_2 43 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 284 (accept_3_2 40 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 284 (accept_3_2 37 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 284 (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 284 (accept_3_2 34 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 284
  (Polychromatic418967fa.accept_15_2_3_14_1_972 32 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 284 (accept_3_2 31 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 284 (accept_3_2 28 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 284 (accept_3_2 25 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 284 (accept_3_2 22 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 284 (Polychromatic418967fa.accept_17_4_8_12_1_9165 21 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 284 (accept_3_2 19 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 284 (accept_3_2 16 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 284
  (Polychromatic418967fa.accept_20_14_13_4_1_11874 14 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 93 284 (accept_3_2 13 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 93 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 284 (accept_3_2 10 93 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 9
  93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 284 (accept_3_2 7 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 284 (accept_3_2 4 93 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 284 (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 93 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 93
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 284 (accept_3_2 1 93 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 284
  (allA_succ_of_accept 91 92 284 (accept_3_2 91 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 92
  284 2 45 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  89 92 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 89 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 92 284 4 22 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 92 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 92 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 92 284 2 43 46 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 92 284 (accept_3_2 85 92 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 92 284 4 21 23 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 92 284
  (Polychromatic418967fa.accept_18_11_2_14_1_3351 83 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 92 284 2 41 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 92 284 (Polychromatic418967fa.accept_13_3_1_11_1_1268 81 92 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 92 284 4 20 23 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 92 284 (accept_3_2 79 92 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 92 284 2 39 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 92 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 77
  92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 92 284 4 19 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 92 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 92 284 2 37 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 92 284 (accept_3_2 73 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 92 284 4 18 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 92 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 92 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 284 2 35 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 69
  92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 284 4 17 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 284 (accept_3_2 67
  92 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 284 2 33 46 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 284
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 284 4 16 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 284 (Polychromatic418967fa.accept_15_3_2_14_1_1713 63 92 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 284 2 31 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 284 (accept_3_2 61 92 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 284 4 15 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 92 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 284 2 29 46 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 284 4 14 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 284 (accept_3_2 55 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  284 2 27 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 92 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 284 4 13 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 92 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 284 2 25 46 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 284 (accept_3_2 49 92 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 284 4 12 23 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 284 2 23 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 92 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 92 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 284 4 11 23 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 284 (accept_3_2 43 92 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 284 2 21 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 284 (Polychromatic418967fa.accept_19_3_16_18_1_2683
  41 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 284 4 10 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 284 2 19 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 92 284 (accept_3_2 37 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 92 284 4 9 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 92 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 284 2 17 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33
  92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 284 4 8 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 284 (accept_3_2 31
  92 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 284 2 15 46 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 284
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 29 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 284 4 7 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 92 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 284 2 13 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 284 (accept_3_2 25 92 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 284 4 6 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 92 284 (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 92 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 284 2 11 46 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 284 4 5 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 284 (accept_3_2 19 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  284 2 9 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 284 4 4 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 92 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 284 2 7 46 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 284 (accept_3_2 13 92 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 284 4 3 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 92 284 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 92 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 284 2 5 46 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 284
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 284 4 2 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 284 (accept_3_2 7 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 284
  2 3 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 92 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 284 4 1 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 92 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 284 2 1 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 284 (accept_3_2 1 92 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 284
  (allA_of_3_0 91 91 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 90 284 (allA_succ_of_accept 89 90 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 89 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 90 284 2 44 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 90 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 90 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 284 2 43 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 284 (accept_3_2 85 90 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 284 2 42 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 284 (Polychromatic418967fa.accept_16_3_10_12_1_4814
  83 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90 284 2 41 45 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 90 284
  (Polychromatic418967fa.accept_11_4_2_9_1_496 81 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 90 284 2 40 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 90 284 (accept_3_2 79 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 284 2 39 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 284 (Polychromatic418967fa.accept_16_13_10_12_1_1811 77 90 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 284 2 38 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 284 2 37 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 90 284 (accept_3_2 73 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 284 2 36 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 90 284 (Polychromatic418967fa.accept_20_11_10_4_1_7520 71 90 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 284 2 35 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 90 284 2 34 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 90 284 (accept_3_2 67 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 284 2 33 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 90 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 90 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 284 2 32 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 284 2 31 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 90 284 (accept_3_2 61 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 284 2 30 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 90 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 284 2 29 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 284 2 28 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 90 284 (accept_3_2 55 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 284 2 27 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 90 284 (Polychromatic418967fa.accept_13_1_12_11_1_728 53 90 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 284 2 26 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 284 2 25 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 90 284 (accept_3_2 49 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 284 2 24 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 90 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 90 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 284 2 23 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 284 2 22 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 90 284 (accept_3_2 43 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 284 2 21 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 90 284 (Polychromatic418967fa.accept_17_7_5_12_1_1997 41 90 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 284 2 20 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 284 2 19 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 90 284 (accept_3_2 37 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 284 2 18 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 90 284 (Polychromatic418967fa.accept_16_3_10_12_1_4814 35 90 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 284 2 17 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 284 2 16 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 284 (accept_3_2 31 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 284 2 15 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 90 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 90 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 284 2 14 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 284 2 13 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 90 284 (accept_3_2 25 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 284 2 12 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 90 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 90 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 284 2 11 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 284 2 10 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 90 284 (accept_3_2 19 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 284 2 9 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 90 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 284 2 8 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 15
  90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 284 2 7 45 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 284 (accept_3_2 13
  90 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 284 2 6 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 284
  (Polychromatic418967fa.accept_16_11_10_12_1_4832 11 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 284 2 5 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 90 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 284 2 4 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 284 (accept_3_2 7 90 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 284 2 3 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 90 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 284 2 2 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 284 2 1 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 284 (accept_3_2 1 90 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 284
  (allA_succ_of_accept 88 89 284 (accept_3_2 88 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 284 (accept_3_2 85 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 284 (accept_3_2 82 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 284 (Polychromatic418967fa.accept_21_17_5_11_1_7028 80 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 284 (accept_3_2 79 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 89 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 284
  (Polychromatic418967fa.accept_8_5_1_4_1_628 77 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 284 (accept_3_2 76 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 284 (accept_3_2 73 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 284 (accept_3_2 70 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 68 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 284 (accept_3_2 67 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 284 (accept_3_2 64 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 284 (accept_3_2 61 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 284
  (Polychromatic418967fa.accept_17_8_4_12_1_1994 59 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 284 (accept_3_2 58 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 284 (accept_3_2 55 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 284
  (Polychromatic418967fa.accept_8_5_1_4_1_628 53 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 284 (accept_3_2 52 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 284 (accept_3_2 49 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 284 (accept_3_2 46 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 284 (accept_3_2 43 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 284 (accept_3_2 40 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 284 (accept_3_2 37 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 284
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 284 (accept_3_2 34 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 284 (accept_3_2 31 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 89 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 284 (accept_3_2 28 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 284 (accept_3_2 25 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 284 (accept_3_2 22 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 284 (accept_3_2 19 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 284
  (Polychromatic418967fa.accept_19_17_13_18_1_9542 17 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 89 284 (accept_3_2 16 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 89 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 284 (accept_3_2 13 89 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 12
  89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 284 (accept_3_2 10 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 284 (accept_3_2 7 89 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 89 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 284
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 284 (accept_3_2 4 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 89 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 284 (accept_3_2 1 89 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 284 (allA_of_3_0 88 88 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 87 284
  (allA_succ_of_accept 86 87 284 (Polychromatic418967fa.accept_13_8_9_11_1_1265 86 87 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 284 (accept_3_2 85 87 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 83
  87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 284 (accept_3_2 82 87
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 284
  (Polychromatic418967fa.accept_10_1_7_4_1_968 81 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 87 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 284 (accept_3_2 79 87 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 284 (accept_3_2 76 87
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 284 (Polychromatic418967fa.accept_8_3_7_4_1_42
  75 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 74 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 284 (accept_3_2 73 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 284 (accept_3_2 70 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 284
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 68 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 284 (accept_3_2 67 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 284 (accept_3_2 64 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 284 (accept_3_2 61 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 284 (Polychromatic418967fa.accept_13_8_9_11_1_1265 60 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 284 (accept_3_2 58 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 284 (accept_3_2 55 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 284 (accept_3_2 52 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 284 (accept_3_2 49 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 284 (accept_3_2 46 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 284 (accept_3_2 43 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 284 (accept_3_2 40 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 284 (accept_3_2 37 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 284 (accept_3_2 34 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 284 (accept_3_2 31 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 284 (accept_3_2 28 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 284 (accept_3_2 25 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 284 (accept_3_2 22 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 284 (accept_3_2 19 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 284 (accept_3_2 16 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 284
  (Polychromatic418967fa.accept_13_1_9_11_1_703 14 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 284 (accept_3_2 13 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 284 (accept_3_2 10 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 87 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 284 (accept_3_2 7 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 284 (accept_3_2 4 87 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  87 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 284 (accept_3_2 1 87 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 284
  (allA_succ_of_accept 85 86 284 (accept_3_2 85 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 86
  284 2 42 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  83 86 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 86 284 2 41 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 86 284 (Polychromatic418967fa.accept_13_3_8_11_1_1906 81 86 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 86 284 2 40 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 86 284 (accept_3_2 79 86 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 86 284 2 39 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 86 284
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 86 284 2 38 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 86 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 86 284 2 37 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 86 284 (accept_3_2 73 86 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86 284 2 36 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 86 284 (Polychromatic418967fa.accept_12_11_2_8_1_511
  71 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 86 284 2 35 43 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 86 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 86 284 2 34 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 86 284 (accept_3_2 67 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 86 284 2 33 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 86 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 86 284 2 32 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 86 284
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 86 284 2 31 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 86 284 (accept_3_2 61 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 86 284 2 30 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 86 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 284 2 29 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 284
  (Polychromatic418967fa.accept_15_12_11_14_1_3464 57 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 86 284 2 28 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 86 284 (accept_3_2 55 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 86 284 2 27 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 86 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 284 2 26 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 284
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 51 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 284 2 25 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 86 284 (accept_3_2 49 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 86 284 2 24 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 86 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 284 2 23 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 284 2 22 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 86 284 (accept_3_2 43 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 86 284 2 21 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 86 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 284 2 20 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 284
  (Polychromatic418967fa.accept_25_14_11_9_1_17396 39 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 86 284 2 19 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 86 284 (accept_3_2 37 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 86 284 2 18 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 86 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 284 2 17 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 284 2 16 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 86 284 (accept_3_2 31 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 86 284 2 15 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 86 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 284 2 14 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 284 2 13 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 86 284 (accept_3_2 25 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 86 284 2 12 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 86 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 284 2 11 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 284
  (Polychromatic418967fa.accept_19_2_10_18_1_6691 21 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 284 2 10 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 86 284 (accept_3_2 19 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 86 284 2 9 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 86 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 86 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 284 2 8 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 284 2 7 43 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 284 (accept_3_2 13
  86 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 284 2 6 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 86 284
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 86 284 2 5 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 86 284 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 86 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 284 2 4 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 284 (accept_3_2 7 86 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 86 284 2 3 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 86 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 86 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 284 2 2 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 284 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3
  86 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 284 2 1 43 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 284 (accept_3_2 1 86
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 284
  (allA_of_3_0 85 85 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 284 (allA_succ_of_accept 83 84 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 84 284 2 41 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 284 (Polychromatic418967fa.accept_15_6_9_14_1_3457 81 84 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 284 4 20 21 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 284 (accept_3_2 79 84 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 284 2 39 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 284 (Polychromatic418967fa.accept_16_13_4_12_1_1805
  77 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 284 4 19 21 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 284
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 75 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 284 2 37 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 284 (accept_3_2 73 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 284 4 18 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 84 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 284 2 35 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 69
  84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 284 4 17 21 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 284 (accept_3_2 67
  84 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 284 2 33 42 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 284 4 16 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 284 (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 84 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 284 2 31 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 284 (accept_3_2 61 84 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 284 4 15 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 284 (Polychromatic418967fa.accept_16_11_4_12_1_1760 59 84
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 284 2 29 42 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 284
  (Polychromatic418967fa.accept_11_2_7_9_1_890 57 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 284 4 14 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 284 (accept_3_2 55 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  284 2 27 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 84 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 284 4 13 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 284 2 25 42 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 284 (accept_3_2 49 84 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 284 4 12 21 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 284 2 23 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 84 284 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 84 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 284 4 11 21 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 284 (accept_3_2 43 84 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 284 2 21 42 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 284
  (Polychromatic418967fa.accept_16_9_4_12_1_4896 41 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 284 4 10 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 84 284 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 84 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 284 2 19 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 284 (accept_3_2 37 84 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 284 4 9 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 84 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 284 2 17 42 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 284 4 8 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 284 (accept_3_2 31 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84
  284 2 15 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 84 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 84 284 4 7 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 84 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 84 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 284 2 13 42 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 284 (accept_3_2 25 84 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 284 4 6 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 284 (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 84 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 284 2 11 42 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 284
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 284 4 5 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 284 (accept_3_2 19 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  284 2 9 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 284 4 4 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 284 2 7 42 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 284 (accept_3_2 13 84 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 284 4 3 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 284 2 5 42 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 284
  (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 284 4 2 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 284 (accept_3_2 7 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 284
  2 3 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 84 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 84 284 4 1 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 84 284 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 84 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 284 2 1 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 284 (accept_3_2 1 84 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 284
  (allA_succ_of_accept 82 83 284 (accept_3_2 82 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 284 (accept_3_2 79 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 284
  (Polychromatic418967fa.accept_10_7_3_4_1_978 77 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 284 (accept_3_2 76 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 284 (accept_3_2 73 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 284 (accept_3_2 70 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 284 (accept_3_2 67 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 284 (accept_3_2 64 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 284 (accept_3_2 61 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 284 (accept_3_2 58 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 284 (Polychromatic418967fa.accept_16_8_3_12_1_1819 56 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 284 (accept_3_2 55 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 83 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 284 (accept_3_2 52 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 284 (accept_3_2 49 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 284 (accept_3_2 46 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 284 (accept_3_2 43 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 284
  (Polychromatic418967fa.accept_16_9_3_12_1_1802 41 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 284 (accept_3_2 40 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 284 (accept_3_2 37 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 284 (accept_3_2 34 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 284 (Polychromatic418967fa.accept_13_6_5_11_1_1971 32 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 284 (accept_3_2 31 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 83 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 284
  (Polychromatic418967fa.accept_10_9_3_4_1_985 29 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 284 (accept_3_2 28 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 284 (accept_3_2 25 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 284 (accept_3_2 22 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 284 (Polychromatic418967fa.accept_13_7_5_11_1_1927 20 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 284 (accept_3_2 19 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 284 (Polychromatic418967fa.accept_17_1_15_12_1_7907 18 83
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 284 (accept_3_2 16 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 284 (accept_3_2 13 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 284
  (Polychromatic418967fa.accept_19_11_7_18_1_5284 11 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 284 (accept_3_2 10 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 284 (accept_3_2 7 83 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 284 (accept_3_2 4 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 83 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 284 (accept_3_2 1 83 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 284 (allA_of_3_0 82 82 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 284
  (allA_succ_of_accept 80 81 284 (Polychromatic418967fa.accept_13_2_3_11_1_1287 80 81 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 284 (accept_3_2 79 81 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 77
  81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 284 (accept_3_2 76 81
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 284
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 75 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 284 (Polychromatic418967fa.accept_19_17_5_18_1_6646 74 81 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 284 (accept_3_2 73 81 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 284 (Polychromatic418967fa.accept_13_7_3_11_1_280 72 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 284 (accept_3_2 70 81
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 284
  (Polychromatic418967fa.accept_8_5_1_4_1_628 69 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 68 81 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 284 (accept_3_2 67 81 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65
  81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 284 (accept_3_2 64 81
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 284
  (Polychromatic418967fa.accept_14_7_11_4_1_3455 63 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 284 (Polychromatic418967fa.accept_13_10_3_11_1_1923 62 81 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 284 (accept_3_2 61 81 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 284 (Polychromatic418967fa.accept_13_8_3_11_1_3467 60 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 284 (accept_3_2 58 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 284 (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 284 (Polychromatic418967fa.accept_16_8_1_12_1_984 56 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 284 (accept_3_2 55 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 284 (accept_3_2 52 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 284 (Polychromatic418967fa.accept_19_13_5_18_1_8106 51 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 50 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 284 (accept_3_2 49 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 284 (Polychromatic418967fa.accept_19_10_5_18_1_10817 48 81
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 284 (accept_3_2 46 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 284 (Polychromatic418967fa.accept_13_5_3_11_1_1288 44 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 284 (accept_3_2 43 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 284 (accept_3_2 40 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 284 (Polychromatic418967fa.accept_15_8_6_14_1_975 38 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 284 (accept_3_2 37 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 284 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 284 (accept_3_2 34 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 284 (Polychromatic418967fa.accept_13_7_3_11_1_280 33 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 284 (Polychromatic418967fa.accept_19_13_5_18_1_8106 32 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 284 (accept_3_2 31 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 81 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 284 (accept_3_2 28 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 284 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 284 (Polychromatic418967fa.accept_21_5_18_11_1_7041 26 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 284 (accept_3_2 25 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 81 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 284 (accept_3_2 22 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 284 (Polychromatic418967fa.accept_13_7_3_11_1_280 20 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 284 (accept_3_2 19 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 284 (accept_3_2 16 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 284 (Polychromatic418967fa.accept_13_1_3_11_1_1289 14 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 284 (accept_3_2 13 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 284 (Polychromatic418967fa.accept_21_12_18_11_1_10051 12 81
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 284 (accept_3_2 10 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 284 (Polychromatic418967fa.accept_13_8_3_11_1_3467 8 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 284 (accept_3_2 7 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 81 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 284 (accept_3_2 4 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  284 (Polychromatic418967fa.accept_18_3_9_14_1_2219 3 81 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 284 (accept_3_2 1 81 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 284 (allA_succ_of_accept 79 80 284 (accept_3_2 79 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 80 284 2 39 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 80 284 (Polychromatic418967fa.accept_14_7_10_4_1_130 77 80 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 80 284 4 19 20 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 80 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 80 284 2 37 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 80 284 (accept_3_2 73 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 80 284 4 18 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 80 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 80 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 80 284 2 35 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 80 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 69
  80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 284 4 17 20 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 284 (accept_3_2 67
  80 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 284 2 33 40 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 80 284 4 16 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 80 284 (Polychromatic418967fa.accept_14_7_10_4_1_130 63 80 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 284 2 31 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 284 (accept_3_2 61 80 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 284 4 15 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 284 (Polychromatic418967fa.accept_18_5_8_14_1_1282 59 80 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 284 2 29 40 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 284 4 14 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 284 (accept_3_2 55 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  284 2 27 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 80 284 (Polychromatic418967fa.accept_15_8_5_14_1_986 53 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 284 4 13 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 80 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 284 2 25 40 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 284 (accept_3_2 49 80 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 284 4 12 20 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 80 284 2 23 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 80 284 (Polychromatic418967fa.accept_22_1_14_20_1_9826 45 80 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 80 284 4 11 20 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 284 (accept_3_2 43 80 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 284 2 21 40 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 284 4 10 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 80 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 284 2 19 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 284 (accept_3_2 37 80 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 284 4 9 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 80 284 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 80 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 284 2 17 40 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 284 4 8 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 284 (accept_3_2 31 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  284 2 15 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 80 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 284 4 7 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 80 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 284 2 13 40 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 284 (accept_3_2 25 80 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 284 4 6 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 284 (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 80
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 284 2 11 40 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 284 4 5 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 284 (accept_3_2 19 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  284 2 9 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 284 4 4 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 80 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 284 2 7 40 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 284 (accept_3_2 13 80 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 284 4 3 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 80 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 284 2 5 40 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 284
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 284 4 2 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 284 (accept_3_2 7 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 284
  2 3 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  284 (Polychromatic418967fa.accept_18_5_8_14_1_1282 5 80 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 80 284 4 1 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 284 2 1 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 284 (accept_3_2 1 80 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 284 (allA_of_3_0 79 79 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 284
  (allA_succ_of_accept 77 78 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 77 78 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 284 2 38 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 75
  78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 284 2 37 39 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 284 (accept_3_2 73
  78 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 284 2 36 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 284 2 35 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 78 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 69 78 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 284 2 34 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 284 (accept_3_2 67 78 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 284 2 33 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 65
  78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 284 2 32 39 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 284 2 31 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 78 284 (accept_3_2 61 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 284 2 30 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 78 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 284 2 29 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 284 2 28 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 284 (accept_3_2 55 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 284 2 27 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 78 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 78 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 284 2 26 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 284 2 25 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 78 284 (accept_3_2 49 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 284 2 24 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 78 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 284 2 23 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 284 2 22 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 78 284 (accept_3_2 43 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 284 2 21 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 284 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 78 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 284 2 20 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 284 2 19 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 78 284 (accept_3_2 37 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 284 2 18 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 284 2 17 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 284 2 16 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 78 284 (accept_3_2 31 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 284 2 15 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 284 2 14 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 284 2 13 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 78 284 (accept_3_2 25 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 284 2 12 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 284 (Polychromatic418967fa.accept_17_6_10_12_1_4129 23 78 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 284 2 11 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 284 2 10 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 78 284 (accept_3_2 19 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 284 2 9 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 78 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 284 2 8 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 284 2 7 39 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 284 (accept_3_2 13
  78 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 284 2 6 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 78 284 2 5 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 78 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 78 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 284 2 4 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 284 (accept_3_2 7 78 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 78 284 2 3 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 78 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 78 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 284 2 2 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 284 2 1 39 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 284 (accept_3_2 1 78
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 284
  (allA_succ_of_accept 76 77 284 (accept_3_2 76 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 284 (accept_3_2 73 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 284
  (Polychromatic418967fa.accept_10_1_7_4_1_968 71 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 284 (accept_3_2 70 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 284 (Polychromatic418967fa.accept_16_4_13_12_1_1740 68 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 284 (accept_3_2 67 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 284 (Polychromatic418967fa.accept_13_1_12_11_1_728 66 77
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 284 (accept_3_2 64 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 62 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 284 (accept_3_2 61 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 284 (Polychromatic418967fa.accept_21_18_14_11_1_7035 60 77 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 284
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 59 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 284 (accept_3_2 58 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 284 (Polychromatic418967fa.accept_13_4_12_11_1_5362 56 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 284 (accept_3_2 55 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 284 (Polychromatic418967fa.accept_21_12_14_11_1_3921 54 77
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 284
  (Polychromatic418967fa.accept_10_3_7_4_1_584 53 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 284 (accept_3_2 52 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 284 (accept_3_2 49 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 284 (Polychromatic418967fa.accept_15_3_2_14_1_1713 48 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 284
  (Polychromatic418967fa.accept_16_15_13_12_1_1787 47 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 77 284 (accept_3_2 46 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 284 (Polychromatic418967fa.accept_18_8_5_14_1_3353 44 77
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 284 (accept_3_2 43 77 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 284 (Polychromatic418967fa.accept_10_2_7_4_1_967
  42 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 284 (accept_3_2 40 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 284 (accept_3_2 37 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 284 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 284
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 284 (accept_3_2 34 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 284 (accept_3_2 31 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 284 (Polychromatic418967fa.accept_13_4_12_11_1_5362 30 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 284
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 29 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 284 (accept_3_2 28 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 284 (accept_3_2 25 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 284 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 284
  (Polychromatic418967fa.accept_10_3_7_4_1_584 23 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 284 (accept_3_2 22 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 284 (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 284 (accept_3_2 19 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 284 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 77
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 284 (accept_3_2 16 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 284 (accept_3_2 13 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 284
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 284 (accept_3_2 10 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 284 (Polychromatic418967fa.accept_16_8_13_12_1_3809 8 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 284 (accept_3_2 7 77 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 284 (Polychromatic418967fa.accept_19_6_1_18_1_13556 6 77 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 284
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 284 (accept_3_2 4 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 77 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 284 (accept_3_2 1 77 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 284 (allA_of_3_0 76 76 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 284 (allA_succ_of_accept 74 75
  284 (Polychromatic418967fa.accept_9_2_3_5_1_60 74 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 284 (accept_3_2 73 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 284 (accept_3_2 70 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 284
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 68 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 284 (accept_3_2 67 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 284 (accept_3_2 64 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 284 (accept_3_2 61 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 284 (accept_3_2 58 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 284 (accept_3_2 55 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 284 (accept_3_2 52 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 284 (accept_3_2 49 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 284 (accept_3_2 46 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 45 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 284 (accept_3_2 43 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 284 (accept_3_2 40 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 284 (accept_3_2 37 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 284 (accept_3_2 34 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 284
  (Polychromatic418967fa.accept_24_8_3_20_1_17389 32 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 284 (accept_3_2 31 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 284 (accept_3_2 28 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 284 (accept_3_2 25 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 284 (accept_3_2 22 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 284 (accept_3_2 19 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 284 (accept_3_2 16 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 284
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 284 (accept_3_2 13 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 284 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 284 (accept_3_2 10 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 284 (accept_3_2 7 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 284 (accept_3_2 4 75 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 284 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 75 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  75 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 284 (accept_3_2 1 75 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 284 (allA_succ_of_accept
  73 74 284 (accept_3_2 73 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 284 2 36 37 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 284 2 35 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 74 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 284 2 34 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 284 (accept_3_2 67 74 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 284 2 33 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 284 (Polychromatic418967fa.accept_11_10_8_9_1_492
  65 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 284 2 32 37 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 284
  (Polychromatic418967fa.accept_19_6_17_18_1_8117 63 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 284 2 31 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 74 284 (accept_3_2 61 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 74 284 2 30 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 74 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 74 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 284 2 29 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 284 2 28 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 74 284 (accept_3_2 55 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 74 284 2 27 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 284 2 26 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 284 2 25 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 74 284 (accept_3_2 49 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 74 284 2 24 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 74 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 74 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 284 2 23 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 284
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 45 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 74 284 2 22 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 74 284 (accept_3_2 43 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 74 284 2 21 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 74 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 74 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 284 2 20 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 284 2 19 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 74 284 (accept_3_2 37 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 74 284 2 18 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 74 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 284 2 17 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 284 2 16 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 74 284 (accept_3_2 31 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 74 284 2 15 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 74 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 74 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 284 2 14 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 284
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 284 2 13 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 74 284 (accept_3_2 25 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 74 284 2 12 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 74 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 74 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 284 2 11 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 284 2 10 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 74 284 (accept_3_2 19 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 74 284 2 9 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 74 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 74 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 284 2 8 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 284 2 7 37 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 284 (accept_3_2 13
  74 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 284 2 6 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 74 284
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 74 284 2 5 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 74 284 (Polychromatic418967fa.accept_20_9_14_4_1_4540 9 74 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 284 2 4 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 284 (accept_3_2 7 74 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 74 284 2 3 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 74 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 74 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 284 2 2 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 74
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 284 2 1 37 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 284 (accept_3_2 1 74
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 284 (allA_of_3_0 73 73 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 284 (allA_succ_of_accept 71 72 284
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 71 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 72 284 2 35 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 72 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 284 4 17 18 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 284 (accept_3_2 67 72 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 284 2 33 36 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 284
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 65 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 284 4 16 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 72 284 (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 72 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 284 2 31 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 284 (accept_3_2 61 72 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 284 4 15 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 284 (Polychromatic418967fa.accept_16_11_8_12_1_1767 59 72
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 284 2 29 36 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 72 284 4 14 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 72 284 (accept_3_2 55 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72
  284 2 27 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 72 284 (Polychromatic418967fa.accept_13_1_7_11_1_702 53 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 72 284 4 13 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 72 284 (Polychromatic418967fa.accept_13_12_7_11_1_1935 51 72 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 284 2 25 36 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 284 (accept_3_2 49 72 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 284 4 12 18 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 284 2 23 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 72 284 (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 72 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 284 4 11 18 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 284 (accept_3_2 43 72 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 284 2 21 36 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 284 4 10 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 72 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 72 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 284 2 19 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 284 (accept_3_2 37 72 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 284 4 9 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 72 284 (Polychromatic418967fa.accept_13_9_7_11_1_1292 35 72 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 284 2 17 36 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 284 4 8 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 284 (accept_3_2 31 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  284 2 15 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 72 284 (Polychromatic418967fa.accept_13_3_7_11_1_1904 29 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 284 4 7 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 284 2 13 36 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 284 (accept_3_2 25 72 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 284 4 6 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 72 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 284 2 11 36 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 284
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 284 4 5 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 284 (accept_3_2 19 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  284 2 9 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 284 4 4 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 284 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 72 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 284 2 7 36 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 284 (accept_3_2 13 72 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 284 4 3 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 284
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 72 284 2 5 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 72 284 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 72 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 284 4 2 18 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 284 (accept_3_2 7 72 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 284 2 3 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 284 4 1 18 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 284
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 72 284 2 1 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 284 (accept_3_2 1 72 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 284 (allA_succ_of_accept 70
  71 284 (accept_3_2 70 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 71 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 284 (accept_3_2 67 71 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 65
  71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 284 (accept_3_2 64 71
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12
  63 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 284
  (Polychromatic418967fa.accept_11_7_5_9_1_884 62 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 71 284 (accept_3_2 61 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  71 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 71 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 284 (accept_3_2 58 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 284 (accept_3_2 55 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 284 (Polychromatic418967fa.accept_14_11_1_4_1_4445 53 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 284 (accept_3_2 52 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 284 (accept_3_2 49 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 284 (accept_3_2 46 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 284
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 44 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 284 (accept_3_2 43 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 284 (Polychromatic418967fa.accept_17_7_3_12_1_4098 41 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 284 (accept_3_2 40 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 284 (accept_3_2 37 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 284 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 284 (accept_3_2 34 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 284
  (Polychromatic418967fa.accept_17_15_3_12_1_9179 32 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 284 (accept_3_2 31 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 284 (accept_3_2 28 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 284 (accept_3_2 25 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 284 (Polychromatic418967fa.accept_19_4_14_18_1_5234 23 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 284 (accept_3_2 22 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 284 (accept_3_2 19 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 284 (accept_3_2 16 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 284 (accept_3_2 13 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 284 (accept_3_2 10 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 284
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 8 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 284 (accept_3_2 7 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  284 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 284 (accept_3_2 4 71 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  71 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 284 (accept_3_2 1 71 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 284 (allA_of_3_0 70 70 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 284 (allA_succ_of_accept 68 69 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 284 (accept_3_2 67 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 284 (accept_3_2 64 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 284 (accept_3_2 61 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 284 (Polychromatic418967fa.accept_13_8_4_11_1_3469 60 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 284 (accept_3_2 58 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 284 (accept_3_2 55 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 284 (accept_3_2 52 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 284
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 284 (accept_3_2 49 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 284 (accept_3_2 46 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 284 (accept_3_2 43 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 284 (accept_3_2 40 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 284 (accept_3_2 37 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 284 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 284 (accept_3_2 34 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 284
  (Polychromatic418967fa.accept_13_6_4_11_1_282 32 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 284 (accept_3_2 31 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 284 (accept_3_2 28 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 284 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 284 (accept_3_2 25 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 284 (accept_3_2 22 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 284 (accept_3_2 19 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 284 (accept_3_2 16 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 284
  (Polychromatic418967fa.accept_20_14_9_4_1_7517 14 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 284 (accept_3_2 13 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 284 (accept_3_2 10 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 284 (accept_3_2 7 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  284 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 69 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 284 (accept_3_2 4 69 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 69
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 284 (accept_3_2 1 69 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 284 (allA_succ_of_accept 67 68
  284 (accept_3_2 67 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 284 2 33 34 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 284 4 16 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 284 (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 68 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 284 2 31 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 284 (accept_3_2 61 68 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 284 4 15 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 68 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 284 2 29 34 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 284 4 14 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 284 (accept_3_2 55 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  284 2 27 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 68 284 (Polychromatic418967fa.accept_13_1_3_11_1_1289 53 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 284 4 13 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 68 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 284 2 25 34 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 284 (accept_3_2 49 68 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 284 4 12 17 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 284
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 47 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 284 2 23 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 68 284 (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 68 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 284 4 11 17 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 284 (accept_3_2 43 68 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 284 2 21 34 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 284 4 10 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 68 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 284 2 19 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 284 (accept_3_2 37 68 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 284 4 9 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 68 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 68 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 284 2 17 34 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 284
  (Polychromatic418967fa.accept_13_7_3_11_1_280 33 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 284 4 8 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 284 (accept_3_2 31 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  284 2 15 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 68 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 284 4 7 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 68 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 284 2 13 34 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 284 (accept_3_2 25 68 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 284 4 6 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 68 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 284 2 11 34 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 284
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 284 4 5 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 284 (accept_3_2 19 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  284 2 9 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 284 (Polychromatic418967fa.accept_16_1_4_12_1_376 17 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 284 4 4 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 68 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 284 2 7 34 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 284 (accept_3_2 13 68 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 284 4 3 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 68 284 (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 68
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 284 2 5 34 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 284 4 2 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 284 (accept_3_2 7 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 284
  2 3 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  284 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 68 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 284 4 1 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 284 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 68 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 284 2 1 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 284 (accept_3_2 1 68 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  67 284 (allA_of_3_0 67 67 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 284 (allA_succ_of_accept 65 66
  284 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 284 2 32 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 66 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 284 2 31 33 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 284 (accept_3_2 61 66 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 284 2 30 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 284 (Polychromatic418967fa.accept_13_7_1_11_1_732
  59 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 284 2 29 33 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 284 2 28 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 66 284 (accept_3_2 55 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 284 2 27 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 284 2 26 33 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 66 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 66 284 2 25 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 66 284 (accept_3_2 49 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 284 2 24 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 66 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 284 2 23 33 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 284 2 22 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 284 (accept_3_2 43 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 284 2 21 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 66 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 284 2 20 33 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 284 2 19 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 66 284 (accept_3_2 37 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 284 2 18 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 284 2 17 33 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 284 2 16 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 66 284 (accept_3_2 31 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 284 2 15 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 66 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 284 2 14 33 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 284 2 13 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 66 284 (accept_3_2 25 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 284 2 12 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 284 (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 66 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 284 2 11 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 284 2 10 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 66 284 (accept_3_2 19 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 284 2 9 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 284 2 8 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 284 2 7 33 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 284 (accept_3_2 13
  66 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 284 2 6 33 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 66 284 2 5 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 66 284 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 66 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 284 2 4 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 284 (accept_3_2 7 66 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 66 284 2 3 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 66 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 66 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 284 2 2 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  66 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 284 2 1 33 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 284 (accept_3_2 1 66
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 284 (allA_succ_of_accept 64 65 284
  (accept_3_2 64 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 65 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 284 (accept_3_2 61 65 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 284 (Polychromatic418967fa.accept_10_9_5_4_1_966
  59 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 284 (accept_3_2 58
  65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 65 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 284 (accept_3_2 55 65 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 53
  65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 284 (accept_3_2 52 65
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 284 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 65 284 (accept_3_2 49 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  65 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 65 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 284 (accept_3_2 46 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 65 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 65 284 (accept_3_2 43 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  65 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 65 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 284 (accept_3_2 40 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 65 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 284 (accept_3_2 37 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 284 (accept_3_2 34 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 284
  (Polychromatic418967fa.accept_15_2_5_14_1_61 32 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 284 (accept_3_2 31 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 284 (accept_3_2 28 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 65 284 (accept_3_2 25 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  65 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 65 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 284 (accept_3_2 22 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 65 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 65 284 (accept_3_2 19 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  65 284 (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 65 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 284 (accept_3_2 16 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 65 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 65 284 (accept_3_2 13 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  65 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 65 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 65 284 (accept_3_2 10 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 65 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 65 284 (accept_3_2 7 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65
  284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 65 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 65 284 (accept_3_2 4 65 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 65 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  65 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 284 (accept_3_2 1 65 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 284 (allA_of_3_0 64 64 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 284 (allA_succ_of_accept 62 63 284
  (Polychromatic418967fa.accept_15_2_3_14_1_972 62 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 284 (accept_3_2 61 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 284 (Polychromatic418967fa.accept_18_6_9_14_1_9915 60 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 284 (accept_3_2 58 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 63 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 284
  (Polychromatic418967fa.accept_15_11_3_14_1_971 56 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 284 (accept_3_2 55 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 284 (accept_3_2 52 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 284
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 50 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 284 (accept_3_2 49 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 284 (Polychromatic418967fa.accept_23_2_17_8_1_17395 48 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 284 (accept_3_2 46 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 284 (Polychromatic418967fa.accept_14_3_7_4_1_118 45 63 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 284
  (Polychromatic418967fa.accept_26_18_11_24_1_17394 44 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 63 284 (accept_3_2 43 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 63 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 284 (accept_3_2 40 63 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 284 (Polychromatic418967fa.accept_10_9_3_4_1_985
  39 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 284
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 38 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 284 (accept_3_2 37 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 284 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 284 (accept_3_2 34 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 284 (Polychromatic418967fa.accept_20_13_3_4_1_6036 33 63 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 284
  (Polychromatic418967fa.accept_11_10_8_9_1_492 32 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 284 (accept_3_2 31 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 284 (accept_3_2 28 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 284
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 284 (accept_3_2 25 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 284 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 284 (accept_3_2 22 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 63 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 284
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 20 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 284 (accept_3_2 19 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 284 (accept_3_2 16 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 284 (Polychromatic418967fa.accept_23_15_17_8_1_17393 15 63 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 284
  (Polychromatic418967fa.accept_20_14_3_4_1_11915 14 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 284 (accept_3_2 13 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 284 (Polychromatic418967fa.accept_19_12_6_18_1_8095 12 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 284 (accept_3_2 10 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 63 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 284
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 284 (accept_3_2 7 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  284 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 284 (accept_3_2 4 63 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 2
  63 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 284 (accept_3_2 1 63 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 284 (allA_succ_of_accept 61 62 284
  (accept_3_2 61 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 284 2 30 31 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 284 2 29 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 62 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 62 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 284 2 28 31 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 284 (accept_3_2 55 62 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 284 2 27 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53
  62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 284 2 26 31 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 284 2 25 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 62 284 (accept_3_2 49 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 62 284 2 24 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 62 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 62 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 62 284 2 23 31 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 62 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 62 284 2 22 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 62 284 (accept_3_2 43 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 62 284 2 21 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 62 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 62 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 62 284 2 20 31 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 62 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 62 284 2 19 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 62 284 (accept_3_2 37 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 62 284 2 18 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 62 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 62 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 284 2 17 31 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 284 2 16 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 62 284 (accept_3_2 31 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 62 284 2 15 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 62 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 62 284 2 14 31 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 62 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 62 284 2 13 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 62 284 (accept_3_2 25 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 62 284 2 12 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 62 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 62 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 62 284 2 11 31 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 62 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 62 284 2 10 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 62 284 (accept_3_2 19 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 62 284 2 9 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 62 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 62 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 284 2 8 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 62 284 2 7 31 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 62 284 (accept_3_2 13
  62 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62 284 2 6 31 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 62 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 62 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 62 284 2 5 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 62 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 62 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 284 2 4 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 284 (accept_3_2 7 62 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 62 284 2 3 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 62 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 62 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 284 2 2 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 62
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 62 284 2 1 31 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 62 284 (accept_3_2 1 62
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 284 (allA_of_3_0 61 61 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 284 (allA_succ_of_accept 59 60 284
  (Polychromatic418967fa.accept_19_2_3_18_1_12206 59 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 284 2 29 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 60 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 284 4 14 15 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 284 (accept_3_2 55 60 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 284 2 27 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 53
  60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 284 4 13 15 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 284
  (Polychromatic418967fa.accept_11_7_5_9_1_884 51 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 284 2 25 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 60 284 (accept_3_2 49 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 284 4 12 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 60 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 284 2 23 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 284 (Polychromatic418967fa.accept_13_6_8_11_1_5398
  45 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 284 4 11 15 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 284 (accept_3_2 43
  60 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 284 2 21 30 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 284
  (Polychromatic418967fa.accept_21_20_18_11_1_11689 41 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 60 284 4 10 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 60 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 284 2 19 30 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 284 (accept_3_2 37 60 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 284 4 9 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35
  60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 284 2 17 30 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 284
  (Polychromatic418967fa.accept_19_14_3_18_1_6675 33 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 284 4 8 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 284 (accept_3_2 31 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  284 2 15 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 60 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 284 4 7 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 284 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 60 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 284 2 13 30 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 284 (accept_3_2 25 60 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 284 4 6 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 284 (Polychromatic418967fa.accept_13_10_8_11_1_1985 23 60
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 284 2 11 30 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 284 4 5 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 284 (accept_3_2 19 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  284 2 9 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 284 4 4 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 284 (Polychromatic418967fa.accept_19_15_3_18_1_5241 15 60 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 284 2 7 30 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 284 (accept_3_2 13 60 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 284 4 3 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11
  60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 284 2 5 30 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 284
  (Polychromatic418967fa.accept_13_9_8_11_1_725 9 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 284 4 2 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 284 (accept_3_2 7 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 284
  2 3 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  284 (Polychromatic418967fa.accept_17_5_9_12_1_9156 5 60 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 60 284 4 1 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 60 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 284 2 1 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 284 (accept_3_2 1 60 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 60 284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 284
  (allA_succ_of_accept 58 59 284 (accept_3_2 58 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 284 (Polychromatic418967fa.accept_13_4_7_11_1_1981 56 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 284 (accept_3_2 55 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 284 (Polychromatic418967fa.accept_17_3_8_12_1_6573 54 59
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 284
  (Polychromatic418967fa.accept_10_3_9_4_1_960 53 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 284 (accept_3_2 52 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 284 (accept_3_2 49 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 284 (accept_3_2 46 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 284 (Polychromatic418967fa.accept_13_5_7_11_1_3470 44 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 284 (accept_3_2 43 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 284 (Polychromatic418967fa.accept_13_3_7_11_1_1904 42 59
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 284 (accept_3_2 40 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 284 (accept_3_2 37 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 284
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 284 (accept_3_2 34 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 284 (Polychromatic418967fa.accept_29_3_1_23_1_17392 32 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 284 (accept_3_2 31 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 284 (Polychromatic418967fa.accept_13_4_7_11_1_1981 30 59
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 284 (accept_3_2 28 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 284 (accept_3_2 25 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 284 (accept_3_2 22 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 284 (accept_3_2 19 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 284
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 284 (accept_3_2 16 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 284 (accept_3_2 13 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 284 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 284
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 11 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 284 (accept_3_2 10 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 284 (accept_3_2 7 59 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 59 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 284
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 284 (accept_3_2 4 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 59 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 284 (accept_3_2 1 59 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 284 (allA_of_3_0
  58 58 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 284 (allA_succ_of_accept 56 57 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 284 (accept_3_2 55 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 284 (accept_3_2 52 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 284
  (Polychromatic418967fa.accept_16_2_9_12_1_46 50 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 284 (accept_3_2 49 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 284 (accept_3_2 46 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 284 (accept_3_2 43 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 284 (accept_3_2 40 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 284 (Polychromatic418967fa.accept_14_11_1_4_1_4445 39 57 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 284 (accept_3_2 37 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 284 (Polychromatic418967fa.accept_16_4_9_12_1_4829 36 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 284 (accept_3_2 34 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 284 (accept_3_2 31 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 284 (accept_3_2 28 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 284 (Polychromatic418967fa.accept_17_10_6_12_1_11635 27 57 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 284 (accept_3_2 25 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 284 (accept_3_2 22 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 284 (accept_3_2 19 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 284 (accept_3_2 16 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 284
  (Polychromatic418967fa.accept_25_14_7_9_1_17391 14 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 284 (accept_3_2 13 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 284 (accept_3_2 10 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 57 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 284 (accept_3_2 7 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  284 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 284 (accept_3_2 4 57 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 57
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 284 (accept_3_2 1 57 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 284 (allA_succ_of_accept 55 56 284 (accept_3_2 55 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 284 2 27 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 56 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 284 4 13 14 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 56 284 2 25 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 56 284 (accept_3_2 49 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 56 284 4 12 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 56 284 (Polychromatic418967fa.accept_13_8_4_11_1_3469 47 56 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 284 2 23 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 45
  56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 284 4 11 14 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 284 (accept_3_2 43
  56 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 284 2 21 28 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 284
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 56 284 4 10 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 56 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 56 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 284 2 19 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 284 (accept_3_2 37 56 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 284 4 9 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 56 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 284 2 17 28 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 56 284 4 8 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 56 284 (accept_3_2 31 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56
  284 2 15 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 56 284 (Polychromatic418967fa.accept_16_13_8_12_1_2723 29 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 56 284 4 7 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 56 284 (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 56 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 284 2 13 28 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 284 (accept_3_2 25 56 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 284 4 6 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 284 (Polychromatic418967fa.accept_13_10_4_11_1_1969
  23 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 284 2 11 28 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 284 4 5 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 284 (accept_3_2 19 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  284 2 9 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 284 4 4 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 56 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 284 2 7 28 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 284 (accept_3_2 13 56 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 284 4 3 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 284 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 56
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 284 2 5 28 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 284
  (Polychromatic418967fa.accept_16_9_8_12_1_979 9 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 284 4 2 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 284 (accept_3_2 7 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 284
  2 3 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  284 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 56 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 284 4 1 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 284 2 1 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 284 (accept_3_2 1 56 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 284)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 284 (allA_of_3_0 55
  55 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 284 (allA_succ_of_accept 53 54 284
  (Polychromatic418967fa.accept_15_8_9_14_1_4577 53 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 284 2 26 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 54 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 284 2 25 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 284 (accept_3_2 49 54 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 284 2 24 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 284 (Polychromatic418967fa.accept_19_9_16_18_1_3887
  47 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 284 2 23 27 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 284
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 284 2 22 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 54 284 (accept_3_2 43 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 284 2 21 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 54 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 54 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 284 2 20 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 284 2 19 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 54 284 (accept_3_2 37 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 284 2 18 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 284 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 54 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 284 2 17 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 284 2 16 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 54 284 (accept_3_2 31 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 284 2 15 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 54 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 284 2 14 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 284 2 13 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 54 284 (accept_3_2 25 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 284 2 12 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 284 2 11 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 284 2 10 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 54 284 (accept_3_2 19 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 284 2 9 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 284 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 54 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 284 2 8 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 284 2 7 27 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 284 (accept_3_2 13
  54 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 284 2 6 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 284
  (Polychromatic418967fa.accept_29_11_25_23_1_17390 11 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 284 2 5 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 54 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 284 2 4 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 284 (accept_3_2 7 54 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 284 2 3 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 284 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 54 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 284 2 2 27 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 284 2 1 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 284 (accept_3_2 1 54 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 284 (allA_succ_of_accept 52 53 284 (accept_3_2
  52 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 53 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 284 (accept_3_2 49 53 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 47
  53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 284 (accept_3_2 46 53
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 284 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 284
  (Polychromatic418967fa.accept_17_10_2_12_1_1070 44 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 284 (accept_3_2 43 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 284 (accept_3_2 40 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 284 (accept_3_2 37 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 284 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 284 (Polychromatic418967fa.accept_13_9_1_11_1_275 35 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 284 (accept_3_2 34 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 284
  (Polychromatic418967fa.accept_23_9_7_8_1_15906 32 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 284 (accept_3_2 31 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 284 (accept_3_2 28 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 284 (accept_3_2 25 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 284 (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 53 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 284 (accept_3_2 22 53 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 284 (accept_3_2 19 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 284 (Polychromatic418967fa.accept_22_18_9_20_1_6474 18 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 284 (accept_3_2 16 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 284 (accept_3_2 13 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 284 (accept_3_2 10 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 284
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 284 (accept_3_2 7 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  284 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 53 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 284 (accept_3_2 4 53 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  53 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 284 (accept_3_2 1 53 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 284)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 284 (allA_of_3_0 52 52 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 284
  (allA_succ_of_accept 50 51 284 (Polychromatic418967fa.accept_15_5_6_14_1_1721 50 51 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 284 (accept_3_2 49 51 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 284 (accept_3_2 46 51
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 284
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 51 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 284 (accept_3_2 43 51 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41
  51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 284 (accept_3_2 40 51
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 284
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 51 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 284 (accept_3_2 37 51 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 284 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 51 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 284 (accept_3_2 34 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  51 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 51 284 (Polychromatic418967fa.accept_24_8_3_20_1_17389 32 51 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 284 (accept_3_2 31 51 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 284 (accept_3_2 28 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  51 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 51 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 51 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 284 (accept_3_2 25 51 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 51 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 284 (accept_3_2 22 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  51 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 51 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 51 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 284 (accept_3_2 19 51 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 284 (accept_3_2 16 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  51 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 284 (Polychromatic418967fa.accept_13_1_12_11_1_728 14 51 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 284 (accept_3_2 13 51 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 284 (accept_3_2 10 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 51 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 51 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 284 (accept_3_2 7 51 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 284 (accept_3_2 4 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 51 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 284 (accept_3_2 1 51 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 284))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 284 (allA_succ_of_accept
  49 50 284 (accept_3_2 49 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 284 2 24 25 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 284 2 23 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 50 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 50 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 284 2 22 25 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 284 (accept_3_2 43 50 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 284 2 21 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 41
  50 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 284 2 20 25 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 284
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 284 2 19 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 50 284 (accept_3_2 37 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 50 284 2 18 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 50 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 50 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 284 2 17 25 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 284 2 16 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 50 284 (accept_3_2 31 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 284 2 15 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 50 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 284 2 14 25 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 284
  (Polychromatic418967fa.accept_28_27_22_4_1_17388 27 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 50 284 2 13 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 50 284 (accept_3_2 25 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 50 284 2 12 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 50 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 50 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 284 2 11 25 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 284
  (Polychromatic418967fa.accept_15_6_5_14_1_429 21 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 284 2 10 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 50 284 (accept_3_2 19 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 50 284 2 9 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 50 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 50 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 284 2 8 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 284 (Polychromatic418967fa.accept_16_15_2_12_1_1799
  15 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 284 2 7 25 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 284 (accept_3_2 13
  50 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 284 2 6 25 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 284
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 50 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 284 2 5 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 284 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 50 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 284 2 4 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 284 (accept_3_2 7 50 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 50 284 2 3 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 50 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 50 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 284 2 2 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 50
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 284 2 1 25 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 284 (accept_3_2 1 50
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 284))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 284 (allA_of_3_0 49 49 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 284
  (allA_succ_of_accept 47 48 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 284 2 23 24 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 45
  48 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 284 4 11 12 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 284 (accept_3_2 43
  48 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 284 2 21 24 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 284
  (Polychromatic418967fa.accept_13_2_9_11_1_258 41 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 48 284 4 10 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 48 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 48 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 284 2 19 24 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 284 (accept_3_2 37 48 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 284 4 9 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 48 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 284 2 17 24 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 284 4 8 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 284 (accept_3_2 31 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  284 2 15 24 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 48 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 284 4 7 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 284 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 48 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 284 2 13 24 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 284 (accept_3_2 25 48 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 284 4 6 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 284 2 11 24 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 284
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 284 4 5 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 284 (accept_3_2 19 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  284 2 9 24 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 284 4 4 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 284 2 7 24 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 284 (accept_3_2 13 48 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 284 4 3 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 48 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 284 2 5 24 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 284 4 2 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 284 (accept_3_2 7 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 284
  2 3 24 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 48 284 4 1 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 48 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 284 2 1 24 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 284 (accept_3_2 1 48 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 284)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 284 (allA_succ_of_accept 46
  47 284 (accept_3_2 46 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 284 (accept_3_2 43 47 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 284 (accept_3_2 40 47
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 284 (Polychromatic418967fa.accept_6_3_5_2_1_12
  39 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 284 (accept_3_2 37 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 284 (accept_3_2 34 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 284 (accept_3_2 31 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 284 (accept_3_2 28 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 284 (accept_3_2 25 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 284 (accept_3_2 22 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 284 (accept_3_2 19 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 284 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 284 (accept_3_2 16 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 284 (accept_3_2 13 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 284 (accept_3_2 10 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 284 (accept_3_2 7 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 284 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 47 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 284 (accept_3_2 4 47 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  47 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 284 (accept_3_2 1 47 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 284))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  284 (allA_of_3_0 46 46 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 284 (allA_succ_of_accept 44 45 284
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 44 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 284 (accept_3_2 43 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 284 (accept_3_2 40 45 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 45 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 284
  (Polychromatic418967fa.accept_27_11_18_14_1_9922 38 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 45 284 (accept_3_2 37 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 45 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 284 (accept_3_2 34 45 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 33
  45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 284
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 284 (accept_3_2 31 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 284 (accept_3_2 28 45 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 284
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 284 (accept_3_2 25 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 284 (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 284 (accept_3_2 22 45 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 284 (accept_3_2 19 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 284 (accept_3_2 16 45 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 284
  (Polychromatic418967fa.accept_17_14_11_12_1_4109 14 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 45 284 (accept_3_2 13 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 284 (Polychromatic418967fa.accept_19_12_7_18_1_8110 12 45 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 284 (accept_3_2 10 45 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 9
  45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 284 (accept_3_2 7 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 284 (accept_3_2 4 45 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 284 (Polychromatic418967fa.accept_18_3_9_14_1_2219 3 45 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 284 (Polychromatic418967fa.accept_20_2_5_4_1_3256 2
  45 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 284 (accept_3_2 1 45 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 284))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  284 (allA_succ_of_accept 43 44 284 (accept_3_2 43 44 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 284 2 21 22 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 44 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 44 284 4 10 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 44 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 39
  44 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 284 2 19 22 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 284 (accept_3_2 37
  44 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 284 4 9 11 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 284
  (Polychromatic418967fa.accept_21_14_2_11_1_8625 35 44 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 44 284 2 17 22 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 44 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 44 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 44 284 4 8 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 44 284 (accept_3_2 31 44 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44 284 2 15 22 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 44 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 44 284 4 7 11 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 44 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 44 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 44 284 2 13 22 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 44 284 (accept_3_2 25 44 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 44 284 4 6 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 44 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 44 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 284 2 11 22 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 21
  44 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 284 4 5 11 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 284 (accept_3_2 19
  44 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 284 2 9 22 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 44 284
  (Polychromatic418967fa.accept_19_17_6_18_1_17387 17 44 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 284 4 4 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 44 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 284 2 7 22 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 284 (accept_3_2 13 44 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 284 4 3 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 284 2 5 22 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 284
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 44 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 284 4 2 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 284 (accept_3_2 7 44 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 284
  2 3 22 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 284 4 1 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 44 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 284 2 1 22 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 284 (accept_3_2 1 44 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 284)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 284 (allA_of_3_0 43 43 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 284 (allA_succ_of_accept 41 42 284
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 42 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 284 2 20 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 42 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 284 2 19 21 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 284 (accept_3_2 37 42 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 284 2 18 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35
  42 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 284 2 17 21 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 284 2 16 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 284 (accept_3_2 31 42 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 284 2 15 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 42 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 284 2 14 21 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 42 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 42 284 2 13 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 42 284 (accept_3_2 25 42 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 284 2 12 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 284 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 42 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 284 2 11 21 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 284 2 10 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 42 284 (accept_3_2 19 42 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 284 2 9 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 284 2 8 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 15
  42 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 284 2 7 21 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 284 (accept_3_2 13
  42 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 284 2 6 21 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 284 2 5 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 42 284 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 284 2 4 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 284 (accept_3_2 7 42 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 42 284 2 3 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 42 284 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 42 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 284 2 2 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 284 2 1 21 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 284 (accept_3_2 1 42
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 284)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41
  284 (allA_succ_of_accept 40 41 284 (accept_3_2 40 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 41 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 284 (accept_3_2 37 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 284 (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 41 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 284
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 284 (accept_3_2 34 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 32 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 284 (accept_3_2 31 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 41 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 284
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 284 (accept_3_2 28 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 284 (accept_3_2 25 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 284 (accept_3_2 22 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 284 (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 41 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 284 (accept_3_2 19 41 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 284 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 41
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 284 (accept_3_2 16 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 284 (accept_3_2 13 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 284
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 11 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 284 (accept_3_2 10 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 284 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 284 (accept_3_2 7 41 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 284 (Polychromatic418967fa.accept_19_6_3_18_1_5262 6 41 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 284 (accept_3_2 4 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 41 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 284 (accept_3_2 1 41 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 284))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 284 (allA_of_3_0 40 40 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 284 (allA_succ_of_accept 38 39 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 284 (accept_3_2 37 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 284 (accept_3_2 34 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 39 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 284
  (Polychromatic418967fa.accept_19_13_1_18_1_5279 32 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 284 (accept_3_2 31 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 284 (accept_3_2 28 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 39 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 284 (accept_3_2 25 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 284 (accept_3_2 22 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 284 (Polychromatic418967fa.accept_14_7_11_4_1_3455 21 39 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 284 (accept_3_2 19 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 284 (accept_3_2 16 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 284
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 284 (accept_3_2 13 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 284 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 284 (accept_3_2 10 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 284 (Polychromatic418967fa.accept_17_9_5_12_1_6606 9 39 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 284 (accept_3_2 7 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  284 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 39 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 284 (accept_3_2 4 39 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 39
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 284 (accept_3_2 1 39 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 284))))))))))))))))))))))))))))))))))))))) (allB_succ 38 284
  (allA_succ_of_accept 37 38 284 (accept_3_2 37 38 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  284 2 18 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 38 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 284 2 17 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 38 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 284 2 16 19 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 284 (accept_3_2 31 38 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 284 2 15 19 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 38 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 284 2 14 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 38 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 38 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 284 2 13 19 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 284 (accept_3_2 25 38 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 284 2 12 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 284 (Polychromatic418967fa.accept_12_11_2_8_1_511
  23 38 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 284 2 11 19 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 38 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 284 2 10 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 38 284 (accept_3_2 19 38 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 38 284 2 9 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 38 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 38 284 2 8 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 38 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  38 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 284 2 7 19 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 284 (accept_3_2 13
  38 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 284 2 6 19 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 38 284
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 38 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 38 284 2 5 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 38 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 38 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 38 284 2 4 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 38 284 (accept_3_2 7 38 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 38 284 2 3 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 38 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 38 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 38 284 2 2 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 38 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 284 2 1 19 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 284 (accept_3_2 1 38
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 284)))))))))))))))))))))))))))))))))))))) (allB_succ 37 284
  (allA_of_3_0 37 37 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 284 (allA_succ_of_accept 35 36 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 36 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 284 2 17 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 36 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 284 4 8 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 284 (accept_3_2 31 36 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 284 2 15 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 284 (Polychromatic418967fa.accept_13_3_10_11_1_1293 29 36
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 284 4 7 9 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 284
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 36 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 284 2 13 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 36 284 (accept_3_2 25 36 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 284 4 6 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 284 (Polychromatic418967fa.accept_15_8_6_14_1_975 23 36 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 284 2 11 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 284 (Polychromatic418967fa.accept_13_8_10_11_1_2730
  21 36 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 284 4 5 9 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 284 (accept_3_2 19
  36 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 284 2 9 18 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 36 284 4 4 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 36 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 36 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 284 2 7 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 284 (accept_3_2 13 36 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 284 4 3 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 36 284 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 36 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 284 2 5 18 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 36 284
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 36 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 36 284 4 2 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 36 284 (accept_3_2 7 36 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 284
  2 3 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36
  284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 284 4 1 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 36 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 284 2 1 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 284 (accept_3_2 1 36 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 284)))))))))))))))))))))))))))))))))))) (allB_succ 35 284 (allA_succ_of_accept 34 35 284
  (accept_3_2 34 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 284 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 35 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 284 (accept_3_2 31 35 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 35 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 284 (accept_3_2 28 35
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 284 (Polychromatic418967fa.accept_6_3_5_2_1_12
  27 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 284
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 284 (accept_3_2 25 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 284 (accept_3_2 22 35 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 284 (accept_3_2 19 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 284 (Polychromatic418967fa.accept_14_3_7_4_1_118 17 35 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 284 (accept_3_2 16 35 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 284 (accept_3_2 13 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 284 (accept_3_2 10 35 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 284
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 8 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 284 (accept_3_2 7 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  284 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 284 (Polychromatic418967fa.accept_20_5_15_4_1_7635 5 35 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 284 (accept_3_2 4 35 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  35 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 284 (accept_3_2 1 35 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 284))))))))))))))))))))))))))))))))))) (allB_succ 34 284
  (allA_of_3_0 34 34 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 284 (allA_succ_of_accept 32 33 284
  (Polychromatic418967fa.accept_15_2_3_14_1_972 32 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 284 (accept_3_2 31 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 284 (accept_3_2 28 33 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 284 (accept_3_2 25 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 284 (Polychromatic418967fa.accept_16_8_1_12_1_984 24 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 284 (accept_3_2 22 33 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 284 (accept_3_2 19 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 284 (accept_3_2 16 33 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 284
  (Polychromatic418967fa.accept_13_1_7_11_1_702 14 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 284 (accept_3_2 13 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 284 (accept_3_2 10 33 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 284 (accept_3_2 7 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 284 (accept_3_2 4 33 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  33 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 284 (accept_3_2 1 33 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 284))))))))))))))))))))))))))))))))) (allB_succ 32 284
  (allA_succ_of_accept 31 32 284 (accept_3_2 31 32 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  284 2 15 16 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 32 284 (Polychromatic418967fa.accept_25_4_7_9_1_17386 29 32 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 284 4 7 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 32 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 284 2 13 16 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 284 (accept_3_2 25 32 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 284 4 6 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 32 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 284 2 11 16 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 284
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 32 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 284 4 5 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 284 (accept_3_2 19 32 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  284 2 9 16 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 32 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 284 4 4 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 284 (Polychromatic418967fa.accept_24_15_8_20_1_12559 15 32 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 284 2 7 16 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 284 (accept_3_2 13 32 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 284 4 3 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 32 284 (Polychromatic418967fa.accept_25_11_7_9_1_17385
  11 32 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 284 2 5 16 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 284
  (Polychromatic418967fa.accept_19_9_13_18_1_10812 9 32 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 284 4 2 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 284 (accept_3_2 7 32 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 284
  2 3 16 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  284 (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 32 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 284 4 1 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 284 (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 32 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 284 2 1 16 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 284 (accept_3_2 1 32 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 284)))))))))))))))))))))))))))))))) (allB_succ 31 284 (allA_of_3_0 31 31 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 284 (allA_succ_of_accept 29 30 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 284 2 14 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 284 2 13 15 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 284 (accept_3_2 25 30 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 284 2 12 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 284 (Polychromatic418967fa.accept_13_10_4_11_1_1969
  23 30 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 284 2 11 15 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 284
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 30 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 284 2 10 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 30 284 (accept_3_2 19 30 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 284 2 9 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 30 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 284 2 8 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  30 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 284 2 7 15 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 284 (accept_3_2 13
  30 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 284 2 6 15 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 284 2 5 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 30 284 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 284 2 4 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 284 (accept_3_2 7 30 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 30 284 2 3 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 30 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 30 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 284 2 2 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  30 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 284 2 1 15 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 284 (accept_3_2 1 30
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 284)))))))))))))))))))))))))))))) (allB_succ 29 284
  (allA_succ_of_accept 28 29 284 (accept_3_2 28 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 29 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 284 (accept_3_2 25 29 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 284
  (Polychromatic418967fa.accept_10_3_9_4_1_960 23 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 284 (accept_3_2 22 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 284 (Polychromatic418967fa.accept_13_7_3_11_1_280 20 29 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 284 (accept_3_2 19 29 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 29 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 284 (accept_3_2 16 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 29 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 284 (accept_3_2 13 29 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 284
  (Polychromatic418967fa.accept_14_11_1_4_1_4445 11 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 284 (accept_3_2 10 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 284 (accept_3_2 7 29 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 29 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 284 (accept_3_2 4 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 29 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 284 (accept_3_2 1 29 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 284))))))))))))))))))))))))))))) (allB_succ 28 284 (allA_of_3_0 28 28 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 284 (allA_succ_of_accept 26 27 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 26
  27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 284 (accept_3_2 25 27
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 284 (Polychromatic418967fa.accept_7_3_6_4_1_30
  24 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 284 (accept_3_2 22 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 284 (Polychromatic418967fa.accept_13_7_1_11_1_732 20 27 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 284 (accept_3_2 19 27 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 27 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 284 (accept_3_2 16 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 284 (Polychromatic418967fa.accept_21_14_6_11_1_7071 14 27 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 284 (accept_3_2 13 27 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 284 (accept_3_2 10 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 284 (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 27 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 284 (accept_3_2 7 27 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 284 (accept_3_2 4 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 27 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 284 (accept_3_2 1 27 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 284))))))))))))))))))))))))))) (allB_succ 26 284 (allA_succ_of_accept 25 26 284 (accept_3_2
  25 26 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 284 2 12 13 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 26 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 284 2 11 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 26 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 284 2 10 13 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 284 (accept_3_2 19 26 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 284 2 9 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  26 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 284 2 8 13 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 26 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 284 2 7 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 284 (accept_3_2 13 26 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  284 2 6 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 26 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 284 2 5 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 26 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 26 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 284 2 4 13 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 284 (accept_3_2 7 26 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 284 2 3 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 26 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 284 2 2 13 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 26 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 284 2 1 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 284 (accept_3_2 1 26 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  284)))))))))))))))))))))))))) (allB_succ 25 284 (allA_of_3_0 25 25 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 284 (allA_succ_of_accept 23 24 284 (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 24 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 284 2 11 12 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 284 4 5 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 284 (accept_3_2 19 24 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  284 2 9 12 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 284 4 4 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 284 2 7 12 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 284 (accept_3_2 13 24 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 284 4 3 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 284 2 5 12 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 284
  (Polychromatic418967fa.accept_16_9_8_12_1_979 9 24 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 284 4 2 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 284 (accept_3_2 7 24 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 284
  2 3 12 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  284 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 24 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 284 4 1 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 284 2 1 12 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 284 (accept_3_2 1 24 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 24 284)))))))))))))))))))))))) (allB_succ 23 284 (allA_succ_of_accept 22 23 284
  (accept_3_2 22 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 284 (accept_3_2 19 23 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 284 (Polychromatic418967fa.accept_16_2_7_12_1_3793 18 23 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 284
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 284 (accept_3_2 16 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 284 (accept_3_2 13 23 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 284
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 284 (accept_3_2 10 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 284 (Polychromatic418967fa.accept_13_8_10_11_1_2730 8 23 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 284 (accept_3_2 7 23 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 284 (accept_3_2 4 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 284 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 23 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 284 (accept_3_2 1 23 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 284))))))))))))))))))))))) (allB_succ 22 284 (allA_of_3_0 22 22 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 284 (allA_succ_of_accept 20 21 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 284 (accept_3_2 19 21 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 284 (Polychromatic418967fa.accept_12_6_9_8_1_165
  18 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 284 (accept_3_2 16 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 21 284 (Polychromatic418967fa.accept_13_1_8_11_1_724 14 21 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 284 (accept_3_2 13 21 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 21 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 284 (accept_3_2 10 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  21 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 21 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 284 (accept_3_2 7 21 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 284 (accept_3_2 4 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  284 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 21 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 284 (accept_3_2 1 21 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 284))))))))))))))))))))) (allB_succ 20 284 (allA_succ_of_accept 19 20 284
  (accept_3_2 19 20 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 284 2 9 10 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 284 4 4 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 20 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 284 2 7 10 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 284 (accept_3_2 13 20 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 284 4 3 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 20 284 (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 20 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 284 2 5 10 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 20 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 284 4 2 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 284 (accept_3_2 7 20 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 284
  2 3 10 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 20 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 284 4 1 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 20 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 284 2 1 10 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 284 (accept_3_2 1 20 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 284)))))))))))))))))))) (allB_succ 19 284 (allA_of_3_0 19 19 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 284 (allA_succ_of_accept 17 18 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 18 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 284 2 8 9 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 18 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 284 2 7 9 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 284 (accept_3_2 13 18 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  284 2 6 9 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 284 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 18 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 284 2 5 9 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 18 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 284 2 4 9 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 284 (accept_3_2 7 18 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 284 2 3 9 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 18 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 284 2 2 9 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 18 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 284 2 1 9 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 284 (accept_3_2 1 18 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  284)))))))))))))))))) (allB_succ 17 284 (allA_succ_of_accept 16 17 284 (accept_3_2 16 17 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 284
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 17 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 284 (accept_3_2 13 17 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 17 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 284 (accept_3_2 10 17 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 284 (accept_3_2 7 17 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 17 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 284 (accept_3_2 4 17 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  17 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 284 (accept_3_2 1 17 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 284))))))))))))))))) (allB_succ 16 284 (allA_of_3_0 16 16 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 284 (allA_succ_of_accept 14 15 284
  (Polychromatic418967fa.accept_17_14_15_12_1_1921 14 15 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 15 284 (accept_3_2 13 15 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 284 (accept_3_2 10 15 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 9
  15 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 284 (accept_3_2 7 15 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  284 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 15 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 284 (accept_3_2 4 15 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  15 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 284 (accept_3_2 1 15 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 284))))))))))))))) (allB_succ 14 284 (allA_succ_of_accept 13 14
  284 (accept_3_2 13 14 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 284 2 6 7 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 284
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 284 2 5 7 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 284 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 14 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 284 2 4 7 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 284 (accept_3_2 7 14 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 284 2 3 7 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 284 2 2 7 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 284 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3
  14 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 284 2 1 7 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 284 (accept_3_2 1 14
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 284)))))))))))))) (allB_succ 13 284 (allA_of_3_0 13 13 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 284 (allA_succ_of_accept 11 12 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 12 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 284 2 5 6 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 284 4 2 3 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 284 (accept_3_2 7 12 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 284 2 3 6 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 284 (Polychromatic418967fa.accept_21_5_12_11_1_5429 5 12 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 284 4 1 3 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 284 (Polychromatic418967fa.accept_18_3_12_14_1_2232
  3 12 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 284 2 1 6 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 284 (accept_3_2 1 12
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 284)))))))))))) (allB_succ 11 284 (allA_succ_of_accept 10 11
  284 (accept_3_2 10 11 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 284 (accept_3_2 7 11 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 11 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5
  11 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 284 (accept_3_2 4 11 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 11 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 284 (accept_3_2 1 11 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  284))))))))))) (allB_succ 10 284 (allA_of_3_0 10 10 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 284
  (allA_succ_of_accept 8 9 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 9 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 284 (accept_3_2 7 9 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 284 (accept_3_2 4 9 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 9
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 284
  (Polychromatic418967fa.accept_13_2_9_11_1_258 2 9 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 284 (accept_3_2 1 9 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 284)))))))))
  (allB_succ 8 284 (allA_succ_of_accept 7 8 284 (accept_3_2 7 8 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 284 2 3 4 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 284 4 1 2 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 8 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 284 2 1 4 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 284 (accept_3_2 1 8 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 284)))))))) (allB_succ 7 284 (allA_of_3_0 7 7 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 284 (allA_succ_of_accept 5 6 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 6 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 284 2 2 3 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 284 2 1 3 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 284 (accept_3_2 1 6 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 284))))))
  (allB_succ 5 284 (allA_succ_of_accept 4 5 284 (accept_3_2 4 5 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 5 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 284 (accept_3_2 1 5 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 284))))) (allB_succ 4 284 (allA_of_3_0 4 4 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 284 (allA_succ_of_accept 2 3 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 3 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 284 (accept_3_2 1 3 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 284))) (allB_succ 2 284 (allA_succ_of_accept 1 2 284 (accept_3_2 1 2 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 284)) (allB_two
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


