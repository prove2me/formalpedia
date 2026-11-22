-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch280_Segment000
-- name    : Polychromatic418967fa_Branch280_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:51:18.956187+00:00
-- url     : https://prove2.me/theorems/9e8a6fd2-253d-4016-84ad-60ae7e2b48ad
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

def Polychromatic418967fa.branch_280_segment_000 : allB 124 280 :=
  allB_succ 123 280 (allA_succ_of_accept 122 123 280 (accept_3_3 122 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 121 123 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 123 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 120 123
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 280 (accept_3_3 119 123
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 123 280
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 118 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 123 280 (Polychromatic418967fa.accept_16_5_11_8_1_3431 117 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 123 280 (accept_3_3 116 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 115 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 114 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 123 280 (accept_3_3 113 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  112 123 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 112 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 123 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 111 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 123 280 (accept_3_3 110 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 280
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 108 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 123 280 (accept_3_3 107 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 123 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 106 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 123 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 105 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 123 280 (accept_3_3 104 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 102 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 123 280 (accept_3_3 101 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 123 280 (Polychromatic418967fa.accept_13_9_6_7_1_551 100 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 123 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 99 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 123 280 (accept_3_3 98 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 280
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 96 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 123 280 (accept_3_3 95 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 123 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 94 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 123 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 123 280 (accept_3_3 92 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 90 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 123 280 (accept_3_3 89 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 123 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 123 280 (Polychromatic418967fa.accept_13_9_6_7_1_551 87 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 280 (accept_3_3 86 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 123 280 (accept_3_3 83 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 123 280 (Polychromatic418967fa.accept_13_4_6_7_1_2471 82 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 123 280 (Polychromatic418967fa.accept_15_6_3_10_1_2341 81 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 280 (accept_3_3 80 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 78 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 123 280 (accept_3_3 77 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 123 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 123 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 280 (accept_3_3 74 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 280
  (Polychromatic418967fa.accept_21_9_18_7_1_5180 72 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 123 280 (accept_3_3 71 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 123 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 123 280 (Polychromatic418967fa.accept_13_4_6_7_1_2471 69 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 280 (accept_3_3 68 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 123 280 (accept_3_3 65 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 123 280 (Polychromatic418967fa.accept_13_12_6_7_1_1071 64 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 123 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 280 (accept_3_3 62 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 280
  (Polychromatic418967fa.accept_16_12_11_8_1_832 60 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 123 280 (accept_3_3 59 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 123 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 123 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 280 (accept_3_3 56 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 123 280 (accept_3_3 53 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 123 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 123 280 (Polychromatic418967fa.accept_13_12_6_7_1_1071 51 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 280 (accept_3_3 50 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 123 280 (accept_3_3 47 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 123 280 (Polychromatic418967fa.accept_17_12_4_8_1_5073 46 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 123 280 (Polychromatic418967fa.accept_16_13_11_8_1_2449 45 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 280 (accept_3_3 44 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 123 280 (accept_3_3 41 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 123 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 123 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 280 (accept_3_3 38 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 280
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 280 (accept_3_3 35 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 280 (Polychromatic418967fa.accept_21_12_18_7_1_6740 33 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 280 (accept_3_3 32 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 280 (accept_3_3 29 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 280 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 280 (accept_3_3 26 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 280
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 280 (accept_3_3 23 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 280 (accept_3_3 20 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 280 (accept_3_3 17 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 280 (Polychromatic418967fa.accept_21_15_18_7_1_5161 15 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 280 (accept_3_3 14 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 123 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 280 (accept_3_3 11 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 280 (Polychromatic418967fa.accept_21_10_18_7_1_5212 10 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 280 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 280 (accept_3_3 8 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 280 (accept_3_3 5 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 123 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 280 (accept_3_3 2 123 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 123 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 122 280 (allA_of_3_1 122 122 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 121 280
  (allA_succ_of_accept 120 121 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 120 121 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 121 280 (accept_3_3 119 121 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 121 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 118 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 117 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 121 280 (accept_3_3 116 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 115 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 114 121 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 114 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 121 280 (accept_3_3 113 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 121 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 112 121
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 121 280 (accept_3_3 110 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 121 280 (Polychromatic418967fa.accept_18_1_13_10_1_2024 109 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 121 280 (Polychromatic418967fa.accept_16_12_9_8_1_2508 108 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 121 280 (accept_3_3 107 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391
  106 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 121 280 (accept_3_3 104 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 121 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 103 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 121 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 102 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 121 280 (accept_3_3 101 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 121 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694 100 121
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 121 280 (accept_3_3 98 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 121 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 121 280 (accept_3_3 95 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 121 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 94 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 121 280 (accept_3_3 92 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 121 280 (Polychromatic418967fa.accept_18_1_13_10_1_2024 91 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 121 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 90 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 121 280 (accept_3_3 89 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 121 280 (accept_3_3 86 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 121 280 (Polychromatic418967fa.accept_21_1_16_7_1_3763 85 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 121 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 121 280 (accept_3_3 83 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 121 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 121 280 (accept_3_3 80 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 121 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 121 280 (accept_3_3 77 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 121 280 (Polychromatic418967fa.accept_13_11_4_7_1_2419 76 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 280 (accept_3_3 74 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 73 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 280 (Polychromatic418967fa.accept_19_15_7_14_1_11879 72 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 280 (accept_3_3 71 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 280 (accept_3_3 68 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 67 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 121 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 280 (accept_3_3 65 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 64 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 121 280 (accept_3_3 62 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 280 (accept_3_3 59 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 280 (accept_3_3 56 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 280 (accept_3_3 53 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 280 (accept_3_3 50 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 280 (Polychromatic418967fa.accept_13_10_4_7_1_2465 49 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 280 (accept_3_3 47 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 280 (accept_3_3 44 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 280 (accept_3_3 41 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 280 (Polychromatic418967fa.accept_18_4_13_10_1_2064 40 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 280 (accept_3_3 38 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 280 (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 280 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 280 (accept_3_3 35 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 280 (accept_3_3 32 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 280 (Polychromatic418967fa.accept_16_15_9_8_1_2440 31 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 280 (accept_3_3 29 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 280 (accept_3_3 26 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 280 (accept_3_3 23 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 280 (accept_3_3 20 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 280 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 280 (Polychromatic418967fa.accept_19_18_7_14_1_5012 18 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 280 (accept_3_3 17 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 121 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 280 (accept_3_3 14 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 280 (accept_3_3 11 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 280 (accept_3_3 8 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 280 (accept_3_3 5 121 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 280 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 121 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 280 (accept_3_3 2 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 280 (Polychromatic418967fa.accept_16_1_9_8_1_2438 1 121 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 120 280 (allA_succ_of_accept 119 120 280 (accept_3_3 119 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 120 280 2 59 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 120 280 (Polychromatic418967fa.accept_18_9_12_10_1_387 117 120 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 120 280 4 29 30 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 115 120 280 5 23 24 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 114 120 280 2 57 60 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 120 280
  (accept_3_3 113 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 120 280 8 14 15 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 120 280
  (Polychromatic418967fa.accept_17_9_1_8_1_5045 111 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 120 280 10 11 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 120 280 (Polychromatic418967fa.accept_17_7_1_8_1_6280 109 120 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 120 280 4 27 30 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 120 280 (accept_3_3 107 120 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 120 280 2 53 60 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 120 280 5 21 24 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 120 280 8 13 15 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 120 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 103 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 120 280 2 51 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 120 280 (accept_3_3 101 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 120 280 20 5 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 120 280 (Polychromatic418967fa.accept_13_8_3_7_1_2455 99 120 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 120 280 2 49 60 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 120 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 97 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 120 280 8 12 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 95 120 280 5 19 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 94 120 280 2 47 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 120 280 (Polychromatic418967fa.accept_21_9_15_7_1_5156 93 120
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 120 280 4 23 30 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 120 280
  (Polychromatic418967fa.accept_22_3_10_16_1_4578 91 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 120 280 10 9 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 120 280 (accept_3_3 89 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 120 280 8 11 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 120 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 120 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 120 280 2 43 60 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 120 280 5 17 24 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 120 280 4 21 30 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 120 280 (accept_3_3 83
  120 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 120 280 2 41 60 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 120 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 120 280 40 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 120 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 120 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 120 280 2 39 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 120 280 (accept_3_3 77 120 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 120 280 4 19 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 120 280 5 15 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 120 280 2 37 60 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 280
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 73 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 120 280 8 9 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 120 280 (accept_3_3 71 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  120 280 10 7 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 120 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 120 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 120 280 4 17 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 67
  120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 280 2 33 60 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 120 280 5 13 24 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 120 280 8 8 15 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 120 280
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 120 280 2 31 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 120 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 120 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 280 20 3 6 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 280 (accept_3_3 59 120 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 280 2 29 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 280
  (Polychromatic418967fa.accept_25_7_20_5_1_17193 57 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 120 280 8 7 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 55 120 280 5 11 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 120 280 2 27 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 280 (accept_3_3 53 120 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 280 4 13 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 120 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 120 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 280 10 5 12 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 280 8 6 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 120 280 (accept_3_3 47 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  120 280 2 23 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  45 120 280 5 9 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  44 120 280 4 11 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 120 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 120 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 280 2 21 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 280 (accept_3_3 41 120 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 280 40 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 120 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 120 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 280 2 19 60 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 280 4 9 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 120 280 5 7 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 120 280 2 17 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 120 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 120 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 280 8 4 15 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 280 10 3 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 280 (accept_3_3 29 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 280 4 7 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 120 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 120 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 280 2 13 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 280 5 5 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 280 8 3 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 280 (accept_3_3 23 120 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 280 2 11 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 280 (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 120
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 280 20 1 6 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 280
  (Polychromatic418967fa.accept_21_19_15_7_1_3709 19 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 120 280 2 9 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 120 280 (accept_3_3 17 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 280 8 2 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 120 280 5 3 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 120 280 2 7 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 120 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 120 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 280 4 3 30 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 280 (accept_3_3 11 120 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 280 10 1 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9
  120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 280 8 1 15 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 280 2 3 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 120 280 5 1 24 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 120 280 4 1 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 120 280 (Polychromatic418967fa.accept_21_3_15_7_1_5155 3 120 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 280 2 1 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1
  120 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 119 280 (allA_of_3_1 119 119 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 118 280
  (allA_succ_of_accept 117 118 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 117 118 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 118 280 2 58 59 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 118 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 115 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 118 280 2 57 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 118 280 (accept_3_3 113 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 118 280 2 56 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 118 280 (Polychromatic418967fa.accept_17_9_16_8_1_2721 111 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 118 280 2 55 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 118 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 109 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 118 280 2 54 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 118 280 (accept_3_3 107 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 118 280 2 53 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 118 280 (Polychromatic418967fa.accept_19_10_4_14_1_4981 105 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 118 280 2 52 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 118 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 103 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 118 280 2 51 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 118 280 (accept_3_3 101 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 118 280 2 50 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 118 280 (Polychromatic418967fa.accept_13_8_1_7_1_2505 99 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 118 280 2 49 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 118 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 97 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 118 280 2 48 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 118 280 (accept_3_3 95 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 118 280 2 47 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 118 280 (Polychromatic418967fa.accept_15_3_13_10_1_2332 93 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 118 280 2 46 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 118 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 91 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 118 280 2 45 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 118 280 (accept_3_3 89 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 118 280 2 44 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 118 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 87 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 118 280 2 43 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 118 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 85 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 118 280 2 42 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 118 280 (accept_3_3 83 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 118 280 2 41 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 118 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 118 280 2 40 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 118 280
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 79 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 118 280 2 39 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 118 280 (accept_3_3 77 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 118 280 2 38 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 118 280 (Polychromatic418967fa.accept_17_7_16_8_1_7613 75 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 118 280 2 37 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 118 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 118 280 2 36 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 118 280 (accept_3_3 71 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 118 280 2 35 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 118 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 69 118 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 280 2 34 59 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 280 2 33 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 280 (accept_3_3 65 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 280 2 32 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 280 2 31 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 280 2 30 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 280 (accept_3_3 59 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 280 2 29 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 280 2 28 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 280 2 27 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 280 (accept_3_3 53 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 280 2 26 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 280 (Polychromatic418967fa.accept_19_13_4_14_1_11912 51 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 280 2 25 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 280 2 24 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 280 (accept_3_3 47 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 280 2 23 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 280 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 280 2 22 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 280 2 21 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 280 (accept_3_3 41 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 280 2 20 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 280 (Polychromatic418967fa.accept_21_18_13_7_1_9883 39 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 280 2 19 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 280 2 18 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 280 (accept_3_3 35 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 280 2 17 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 280 (Polychromatic418967fa.accept_15_3_13_10_1_2332 33 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 280 2 16 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 280 2 15 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 280 (accept_3_3 29 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 280 2 14 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 280 2 13 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 25 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 280 2 12 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 280 (accept_3_3 23 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 280 2 11 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 280 (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 280 2 10 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 280 2 9 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 118 280 (accept_3_3 17 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 280 2 8 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 118 280 (Polychromatic418967fa.accept_19_15_4_14_1_6400 15 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 280 2 7 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 280
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 118 280 2 6 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 118 280 (accept_3_3 11 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 118 280 2 5 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 118 280 (Polychromatic418967fa.accept_17_9_16_8_1_2721 9 118 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 280 2 4 59 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 280 2 3 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 280 (accept_3_3 5 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  280 2 2 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 118 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 280 2 1 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 118 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 118 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 117 280 (allA_succ_of_accept 116 117 280 (accept_3_3 116 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 115 117 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 117 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 114 117
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 117 280 (accept_3_3 113 117
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 117 280
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 112 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 117 280 (Polychromatic418967fa.accept_15_6_12_10_1_1543 111 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 117 280 (accept_3_3 110 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 117 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 108 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 117 280 (accept_3_3 107 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 117 280 (Polychromatic418967fa.accept_19_11_3_14_1_6375 106 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 117 280 (Polychromatic418967fa.accept_18_15_9_10_1_1082 105 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 117 280 (accept_3_3 104 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  103 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 117 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 102 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 117 280 (accept_3_3 101 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 117 280 (Polychromatic418967fa.accept_16_4_5_8_1_2425 100 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 117 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 99 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 117 280 (accept_3_3 98 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 117 280
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 96 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 117 280 (accept_3_3 95 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 117 280 (Polychromatic418967fa.accept_19_18_3_14_1_5001 94 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 117 280
  (Polychromatic418967fa.accept_16_13_5_8_1_5814 93 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 117 280 (accept_3_3 92 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 117 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 90 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 117 280 (accept_3_3 89 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 117 280 (Polychromatic418967fa.accept_15_13_12_10_1_4352 88 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 117 280
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 87 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 117 280 (accept_3_3 86 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 117 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 117 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 84 117
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 117 280 (accept_3_3 83 117
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 117 280
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 82 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 117 280 (Polychromatic418967fa.accept_15_6_12_10_1_1543 81 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 117 280 (accept_3_3 80 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 117 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 117 280 (accept_3_3 77 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 117 280 (Polychromatic418967fa.accept_16_12_5_8_1_2492 76 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 117 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 75 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 117 280 (accept_3_3 74 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 117 280
  (Polychromatic418967fa.accept_25_22_17_5_1_15606 72 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 117 280 (accept_3_3 71 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 117 280 (Polychromatic418967fa.accept_24_22_21_16_1_15626 70 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 117 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 69 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 117 280 (accept_3_3 68 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 117 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 117 280 (accept_3_3 65 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 64 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 117 280
  (Polychromatic418967fa.accept_24_15_21_16_1_12209 63 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 117 280 (accept_3_3 62 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 117 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 280 (Polychromatic418967fa.accept_16_12_5_8_1_2492 60 117
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 280 (accept_3_3 59 117
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 280
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 58 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 117 280 (Polychromatic418967fa.accept_17_6_15_8_1_1714 57 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 280 (accept_3_3 56 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 117 280 (accept_3_3 53 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 117 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335 52 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 117 280 (Polychromatic418967fa.accept_15_6_12_10_1_1543 51 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 280 (accept_3_3 50 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 280
  (Polychromatic418967fa.accept_18_12_9_10_1_3104 48 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 280 (accept_3_3 47 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 280 (Polychromatic418967fa.accept_19_8_3_14_1_3571 46 117 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 280 (Polychromatic418967fa.accept_16_13_5_8_1_5814 45 117
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 280 (accept_3_3 44 117
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 42 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 280 (accept_3_3 41 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 280 (Polychromatic418967fa.accept_17_6_15_8_1_1714 40 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 280 (accept_3_3 38 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 280
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 280 (accept_3_3 35 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 280 (Polychromatic418967fa.accept_22_12_7_16_1_14142 34 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 280
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 33 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 280 (accept_3_3 32 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 117 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 280 (accept_3_3 29 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 280
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 28 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 280 (Polychromatic418967fa.accept_16_11_5_8_1_2427 27 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 280 (accept_3_3 26 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 24 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 280 (accept_3_3 23 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 280 (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 280 (accept_3_3 20 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 280 (accept_3_3 17 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 280 (Polychromatic418967fa.accept_19_16_3_14_1_9212 16 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 280 (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 280 (accept_3_3 14 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 280
  (Polychromatic418967fa.accept_16_12_5_8_1_2492 12 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 280 (accept_3_3 11 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 280 (Polychromatic418967fa.accept_17_10_15_8_1_6324 10 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 280 (accept_3_3 8 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 280 (accept_3_3 5 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 280 (Polychromatic418967fa.accept_16_4_5_8_1_2425 4 117 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 280 (Polychromatic418967fa.accept_16_3_5_8_1_4543 3 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 280 (accept_3_3 2 117 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 116 280 (allA_of_3_1 116 116 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 115 280
  (allA_succ_of_accept 114 115 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 114 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 115 280 (accept_3_3 113 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 115 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 112 115 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 115 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 111 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 115 280 5 22 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 115 280 (Polychromatic418967fa.accept_13_5_11_7_1_559 109 115 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 115 280
  (Polychromatic418967fa.accept_13_4_11_7_1_558 108 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 115 280 (accept_3_3 107 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 115 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 106 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 105 115 280 5 21 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 104 115 280 (accept_3_3 104 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 115 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 103 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 115 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 102 115
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 115 280 (accept_3_3 101 115
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 115 280 5 20 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 115 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 115 280 (accept_3_3 98 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 115 280 (Polychromatic418967fa.accept_19_2_1_14_1_3663 97 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 115 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 96 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 115 280 5 19 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 115 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 94 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 115 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 115 280 (accept_3_3 92 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 115 280 (Polychromatic418967fa.accept_16_11_3_8_1_4597 91 115 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 115 280 5 18 23 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 115 280 (accept_3_3 89 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 115 280
  (Polychromatic418967fa.accept_17_3_13_8_1_11337 88 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 115 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 115 280 (accept_3_3 86 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 85 115 280 5 17 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 115 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 115 280 (accept_3_3 83 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 115 280 (Polychromatic418967fa.accept_12_10_7_4_1_820
  82 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 115 280 5 16 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 115 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 79 115 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 115 280 (accept_3_3 77 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 115 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 115 280 5 15 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 115 280 (accept_3_3 74 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 115 280 (Polychromatic418967fa.accept_17_5_13_8_1_7556 73 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 280 (Polychromatic418967fa.accept_17_4_13_8_1_3874 72 115
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 280 (accept_3_3 71 115
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 115 280 5 14 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 115 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 280 (accept_3_3 68 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 115 280 5 13 23 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 115 280
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 64 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 115 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 280 (accept_3_3 62 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077 61 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 115 280 5 12 23 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 115 280 (accept_3_3 59
  115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 58 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 115 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 280 (accept_3_3 56 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 115 280 5 11 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 115 280 (Polychromatic418967fa.accept_17_3_13_8_1_11337 54 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 280 (accept_3_3 53 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 280 (Polychromatic418967fa.accept_16_4_3_8_1_2486
  52 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 115 280 5 10 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 115 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 280 (Polychromatic418967fa.accept_9_3_7_1_1_143
  48 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 280 (accept_3_3 47
  115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 280
  (Polychromatic418967fa.accept_12_10_7_4_1_820 46 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 115 280 5 9 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 115 280 (accept_3_3 44 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 280 (Polychromatic418967fa.accept_13_4_11_7_1_558 43 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 280 (accept_3_3 41 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 115 280 5 8 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 115 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 280 (accept_3_3 38 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 280 (Polychromatic418967fa.accept_16_5_3_8_1_4555
  37 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 280
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 115 280 5 7 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 115 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 280 (accept_3_3 32 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 280 (Polychromatic418967fa.accept_9_4_7_1_1_379
  31 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 115 280 5 6 23 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 115 280
  (accept_3_3 29 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 280
  (Polychromatic418967fa.accept_16_12_3_8_1_5729 28 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 115 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 280 (accept_3_3 26 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 115 280 5 5 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 115 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 115 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 280 (accept_3_3 23 115 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 115 280 5 4 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 115 280 (Polychromatic418967fa.accept_21_19_10_7_1_8384 19 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 280 (Polychromatic418967fa.accept_13_5_11_7_1_559
  18 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 280 (accept_3_3 17
  115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 280
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 115 280 5 3 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 115 280 (accept_3_3 14 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 280 (accept_3_3 11 115 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 115 280 5 2 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 115 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 280 (accept_3_3 8 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 280
  (Polychromatic418967fa.accept_22_7_5_16_1_17192 7 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 115 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 115 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 280 5 1 23 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 115 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 280 (accept_3_3 2 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 115 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 114 280 (allA_succ_of_accept 113 114 280 (accept_3_3 113 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 114 280 2 56 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 114 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 111 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 114 280 2 55 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 114 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 109 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 114 280 2 54 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 114 280 (accept_3_3 107 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 114 280 2 53 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 114 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 105 114 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 114 280 2 52 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 114 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 103 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 114 280 2 51 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 114 280 (accept_3_3 101 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 114 280 2 50 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 114 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 99 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 114 280 2 49 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 114 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 97 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 114 280 2 48 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 114 280 (accept_3_3 95 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 114 280 2 47 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 114 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 114 280 2 46 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 114 280
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 91 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 114 280 2 45 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 114 280 (accept_3_3 89 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 114 280 2 44 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 114 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 87 114 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 114 280 2 43 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 114 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 85 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 114 280 2 42 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 114 280 (accept_3_3 83 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 114 280 2 41 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 114 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 114 280 2 40 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 79 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 280 2 39 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 280 (accept_3_3 77 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 114 280 2 38 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 114 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 114 280 2 37 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 280
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 73 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 280 2 36 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 280 (accept_3_3 71 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 114 280 2 35 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 114 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 114 280 2 34 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 280 2 33 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 280 (accept_3_3 65 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 114 280 2 32 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 114 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 114 280 2 31 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 280 2 30 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 280 (accept_3_3 59 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 114 280 2 29 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 114 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 114 280 2 28 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 280
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 55 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 280 2 27 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 280 (accept_3_3 53 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 280 2 26 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 280 2 25 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 280 2 24 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 280 (accept_3_3 47 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 280 2 23 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 280 2 22 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 280 2 21 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 280 (accept_3_3 41 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 280 2 20 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 280 2 19 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 280
  (Polychromatic418967fa.accept_17_3_12_8_1_1688 37 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 280 2 18 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 280 (accept_3_3 35 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 280 2 17 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 280 2 16 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 280 2 15 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 280 (accept_3_3 29 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 280 2 14 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 280 2 13 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 280 2 12 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 280 (accept_3_3 23 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 280 2 11 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 280 2 10 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 280
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 19 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 280 2 9 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 114 280 (accept_3_3 17 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 114 280 2 8 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 114 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 280 2 7 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 280 2 6 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 114 280 (accept_3_3 11 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 280 2 5 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 114 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 114 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 280 2 4 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 280 2 3 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 280 (accept_3_3 5 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114
  280 2 2 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  114 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 114 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 114 280 2 1 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 114 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 1 114 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 113 280 (allA_of_3_1 113 113 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 112 280
  (allA_succ_of_accept 111 112 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 111 112 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 112 280 2 55 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 112 280 (Polychromatic418967fa.accept_15_4_7_10_1_807
  109 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 112 280 4 27 28 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 112 280
  (accept_3_3 107 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 112 280 2 53 56 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 105 112 280 7 15 16 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 104 112 280 8 13 14
  35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 112 280
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 103 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 112 280 2 51 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 112 280 (accept_3_3 101 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 112 280 4 25 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 112 280 (Polychromatic418967fa.accept_22_11_2_16_1_759 99 112 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 112 280 14 7 8 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 112 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 97 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 112 280 8 12 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 112 280 (accept_3_3 95 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 112 280 2 47 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 112 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 93 112 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 112 280 4 23 28 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 91 112 280 7 13 16 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 90 112 280 2 45 56 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 112 280 (accept_3_3 89
  112 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 112 280 8 11 14 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 112 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 87 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 112 280 2 43 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 112 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 85 112 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 112 280 28 3 4 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 112 280 (accept_3_3 83 112 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 112 280 2 41 56 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 112 280
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 81 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 112 280 8 10 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 112 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 112 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 112 280 2 39 56 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 112 280 7 11 16 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 112 280 4 19 28 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 112 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 75 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 112 280 2 37 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 112 280 (Polychromatic418967fa.accept_19_16_17_14_1_4969 73 112 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 112 280 8 9 14 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 112 280 (accept_3_3 71 112 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 112 280 14 5 8 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 112 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 69 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 112 280 4 17 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 112 280 (Polychromatic418967fa.accept_13_2_8_7_1_2424 67 112 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 112 280 2 33 56 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 112 280 (accept_3_3 65 112 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 112 280 8 8 14 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 112 280 7 9 16 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 112 280 2 31 56 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 112 280 4 15 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 112 280 (accept_3_3 59 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 112 280 2 29 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 112 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 112 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 280 56 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135
  55 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 112 280 2 27 56 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 112 280
  (accept_3_3 53 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 112 280 4 13 28 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 112 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 112 280 2 25 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 112 280 7 7 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 112 280 8 6 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 112 280 (accept_3_3 47 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 280 2 23 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 280 (Polychromatic418967fa.accept_25_20_12_5_1_17191 45 112 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 280 4 11 28 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 280 14 3 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 112 280 (accept_3_3 41 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  112 280 8 5 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 112 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 112 280 2 19 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 112 280 (Polychromatic418967fa.accept_29_8_25_19_1_17190 37 112 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 280 4 9 28 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 112 280 7 5 16 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 112 280 2 17 56 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 112 280 8 4 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 112 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 112 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 280 2 15 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 280 (accept_3_3 29 112 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 280 28 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 112
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 280 2 13 56 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 280 8 3 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 112 280 (accept_3_3 23 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  112 280 2 11 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  21 112 280 7 3 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  20 112 280 4 5 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 112 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 112 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 112 280 2 9 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 280 (accept_3_3 17 112 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 280 8 2 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 112 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 112 280 14 1 8 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 112 280
  (Polychromatic418967fa.accept_18_13_4_10_1_1076 13 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 112 280 4 3 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 112 280 (accept_3_3 11 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 112 280 2 5 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 112 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 112 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 280 8 1 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 112 280 7 1 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 112 280 2 3 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 280 (accept_3_3 5 112 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112 280 4 1 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 112 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 112 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 280 2 1 56 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 280
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 112 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 112
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 111 280 (allA_succ_of_accept 110 111 280 (accept_3_3 110 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 109 111 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 111 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 108
  111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 111 280 (accept_3_3 107
  111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 111 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 106 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 111 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 105 111 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 111 280 (accept_3_3 104 111 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 111 280 (Polychromatic418967fa.accept_12_6_3_4_1_394
  102 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 111 280 (accept_3_3
  101 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 111 280
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 100 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 111 280 (Polychromatic418967fa.accept_25_24_11_5_1_17189 99 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 111 280 (accept_3_3 98 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 111 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 96 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 111 280 (accept_3_3 95 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 111 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 111 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 93 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 111 280 (accept_3_3 92 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 111 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 90 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 111 280 (accept_3_3 89 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 111 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 111 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 111 280 (accept_3_3 86 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 111 280
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 84 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 111 280 (accept_3_3 83 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 111 280 (Polychromatic418967fa.accept_24_10_15_16_1_6986 82 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 111 280 (Polychromatic418967fa.accept_16_1_15_8_1_2411 81 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 111 280 (accept_3_3 80 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79
  111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 111 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 111 280 (accept_3_3 77 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 111 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 111 280 (Polychromatic418967fa.accept_19_18_16_14_1_2377 75 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 111 280 (accept_3_3 74 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 111 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 111 280 (accept_3_3 71 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 111 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 111 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 111 280 (accept_3_3 68 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 111 280 (accept_3_3 65 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 111 280 (Polychromatic418967fa.accept_15_4_6_10_1_823 64 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 111 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 111 280 (accept_3_3 62 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 111 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 111 280 (accept_3_3 59 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 111 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 111 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 57 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 111 280 (accept_3_3 56 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 111 280 (accept_3_3 53 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 111 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 111 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 280 (accept_3_3 50 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 280
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 48 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 280 (accept_3_3 47 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 280 (Polychromatic418967fa.accept_17_11_9_8_1_5038 45 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 280 (accept_3_3 44 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 280 (accept_3_3 41 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 280 (accept_3_3 38 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 280
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 280 (accept_3_3 35 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 280 (accept_3_3 32 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 280 (accept_3_3 29 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 280 (accept_3_3 26 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 280 (accept_3_3 23 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 280 (Polychromatic418967fa.accept_19_2_16_14_1_3551 21 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 280 (accept_3_3 20 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 280 (accept_3_3 17 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 280 (accept_3_3 14 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 111 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 280 (accept_3_3 11 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 280 (Polychromatic418967fa.accept_24_10_15_16_1_6986 10 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 280 (Polychromatic418967fa.accept_16_9_15_8_1_3425
  9 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 280 (accept_3_3 8
  111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 111 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 111 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 280 (accept_3_3 5 111 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 111 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 111 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539
  3 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 280 (accept_3_3 2
  111 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 111 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 110 280 (allA_of_3_1 110 110 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 109 280
  (allA_succ_of_accept 108 109 280 (Polychromatic418967fa.accept_16_12_13_8_1_2409 108 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 109 280 (accept_3_3 107 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 109 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 106 109 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 105 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 109 280 (accept_3_3 104 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 109 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 103 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 109 280 (Polychromatic418967fa.accept_13_11_5_7_1_2420 102 109 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 109 280 (accept_3_3 101 109 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 109 280
  (Polychromatic418967fa.accept_16_4_13_8_1_3424 100 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 109 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 99 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 109 280 (accept_3_3 98 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 109 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 97 109 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 109 280
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 96 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 109 280 (accept_3_3 95 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 109 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 94 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 109 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 109 280 (accept_3_3 92 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 109 280 (Polychromatic418967fa.accept_16_11_13_8_1_1578 91 109 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 109 280
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 90 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 109 280 (accept_3_3 89 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 109 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 88 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 109 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 109 280 (accept_3_3 86 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 109 280 (Polychromatic418967fa.accept_16_5_13_8_1_2454 85 109 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 109 280
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 84 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 109 280 (accept_3_3 83 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 109 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 109 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 109 280 (accept_3_3 80 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 109 280 (Polychromatic418967fa.accept_21_16_4_7_1_5191 79 109 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 280
  (Polychromatic418967fa.accept_24_6_13_16_1_10575 78 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 109 280 (accept_3_3 77 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 109 280 (Polychromatic418967fa.accept_13_11_5_7_1_2420 76 109 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 109 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 280 (accept_3_3 74 109 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 109 280
  (Polychromatic418967fa.accept_15_13_4_10_1_821 73 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 109 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 109 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 280 (accept_3_3 71 109 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 109 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 70 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 280 (accept_3_3 68 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 67 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 280 (Polychromatic418967fa.accept_15_6_4_10_1_2319 66 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 280 (accept_3_3 65 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 280 (Polychromatic418967fa.accept_13_12_5_7_1_1696 64 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 280 (accept_3_3 62 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 61 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 280 (Polychromatic418967fa.accept_16_12_13_8_1_2409 60 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 280 (accept_3_3 59 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 280 (accept_3_3 56 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 280 (Polychromatic418967fa.accept_17_4_7_8_1_7491 55 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 280 (accept_3_3 53 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 52 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 280 (accept_3_3 50 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 280 (Polychromatic418967fa.accept_18_13_1_10_1_4331 49 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 280 (accept_3_3 47 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 280 (accept_3_3 44 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 280 (Polychromatic418967fa.accept_22_20_21_16_1_12616 42 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 280 (accept_3_3 41 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 280 (Polychromatic418967fa.accept_21_19_4_7_1_3775 40 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 280 (accept_3_3 38 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 280 (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 280 (accept_3_3 35 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 280 (accept_3_3 32 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 280 (Polychromatic418967fa.accept_17_14_7_8_1_7544 31 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 280 (Polychromatic418967fa.accept_24_6_13_16_1_10575 30 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 280 (accept_3_3 29 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 280 (accept_3_3 26 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 280 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 280 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 280 (accept_3_3 23 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 280 (accept_3_3 20 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 280 (Polychromatic418967fa.accept_16_3_13_8_1_1594 19 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 280 (Polychromatic418967fa.accept_17_1_7_8_1_6347 18 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 280 (accept_3_3 17 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 280 (Polychromatic418967fa.accept_17_16_7_8_1_7638 16 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 280 (accept_3_3 14 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 280 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 280 (accept_3_3 11 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 109
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 280 (accept_3_3 8 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 280 (accept_3_3 5 109 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 109 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 280 (accept_3_3 2 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 280 (Polychromatic418967fa.accept_17_1_7_8_1_6347 1 109 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 108 280 (allA_succ_of_accept 107 108 280 (accept_3_3 107 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 108 280 2 53 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 108 280 (Polychromatic418967fa.accept_16_9_12_8_1_1554 105 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 108 280 4 26 27 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 108 280
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 103 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 108 280 2 51 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 108 280 (accept_3_3 101 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 108 280 4 25 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 108 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 99 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 108 280 2 49 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 108 280
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 97 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 108 280 4 24 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 108 280 (accept_3_3 95 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 108 280 2 47 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 108 280 (Polychromatic418967fa.accept_16_13_12_8_1_2451 93 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 108 280 4 23 27 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 108 280
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 91 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 108 280 2 45 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 108 280 (accept_3_3 89 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 108 280 4 22 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 108 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694 87 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 108 280 2 43 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 280
  (Polychromatic418967fa.accept_16_5_12_8_1_2521 85 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 280 4 21 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 280 (accept_3_3 83 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 108 280 2 41 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 108 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 81 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 108 280 4 20 27 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 280
  (Polychromatic418967fa.accept_16_15_12_8_1_4585 79 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 108 280 2 39 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 108 280 (accept_3_3 77 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 108 280 4 19 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 108 280 (Polychromatic418967fa.accept_13_10_4_7_1_2465 75 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 108 280 2 37 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 280
  (Polychromatic418967fa.accept_11_7_9_5_1_338 73 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 280 4 18 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 280 (accept_3_3 71 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 108 280 2 35 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 108 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 69 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 280 4 17 27 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 280
  (Polychromatic418967fa.accept_15_7_3_10_1_817 67 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 280 2 33 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 280 (accept_3_3 65 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 280 4 16 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 280 (Polychromatic418967fa.accept_13_11_4_7_1_2419 63 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 280 2 31 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 280
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 61 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 280 4 15 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 280 (accept_3_3 59 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 280 2 29 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 280 (Polychromatic418967fa.accept_16_9_12_8_1_1554 57 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 280 4 14 27 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 280
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 280 2 27 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 280 (accept_3_3 53 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 280 4 13 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 51 108 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 280 2 25 54 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 280
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 49 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 280 4 12 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 280 (accept_3_3 47 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 280 2 23 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 280 (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 280 4 11 27 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 280
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 43 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 108 280 2 21 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 108 280 (accept_3_3 41 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 280 4 10 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 280 2 19 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 280
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 280 4 9 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 280 (accept_3_3 35 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  108 280 2 17 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 108 280 (Polychromatic418967fa.accept_16_1_12_8_1_2405 33 108 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 280 4 8 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 280
  (Polychromatic418967fa.accept_16_15_12_8_1_4585 31 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 108 280 2 15 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 108 280 (accept_3_3 29 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 280 4 7 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 108 280 (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 108 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 280 2 13 54 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 280
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 280 4 6 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 280 (accept_3_3 23 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  108 280 2 11 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 108 280 (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 108 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 280 4 5 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 280 (Polychromatic418967fa.accept_13_6_4_7_1_2464
  19 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 280 2 9 54 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 280
  (accept_3_3 17 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 280 4 4 27 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 280
  (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 280 2 7 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 280 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 108 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 280 4 3 27 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 280 (accept_3_3 11
  108 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 280 2 5 54 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 280
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 280 4 2 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 108 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 280 2 3 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 280 (accept_3_3 5 108 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 280 4 1 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 108 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 108 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 280 2 1 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 280
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 108 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 107 280 (allA_of_3_1 107 107 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 106 280
  (allA_succ_of_accept 105 106 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 105 106 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 106 280 2 52 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 106 280 (Polychromatic418967fa.accept_9_4_7_1_1_379
  103 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 106 280 2 51 53 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 106 280
  (accept_3_3 101 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 106 280 2 50 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 106 280
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 99 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 106 280 2 49 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 106 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 97 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 106 280 2 48 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 106 280 (accept_3_3 95 106 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 106 280 2 47 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 106 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 93
  106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 106 280 2 46 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 106 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 91 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 106 280 2 45 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 106 280 (accept_3_3 89 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 106 280 2 44 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 106 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 87 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 106 280 2 43 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 85 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 106 280 2 42 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 106 280 (accept_3_3 83 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 106 280 2 41 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 106 280 (Polychromatic418967fa.accept_15_6_1_10_1_1549 81 106 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 106 280 2 40 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 79 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 106 280 2 39 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 106 280 (accept_3_3 77 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 280 2 38 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 280 2 37 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 280 2 36 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 280 (accept_3_3 71 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 280 2 35 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 280 2 34 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 280 2 33 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 280 (accept_3_3 65 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 280 2 32 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 280 (Polychromatic418967fa.accept_17_12_4_8_1_5073 63 106 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 280 2 31 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 280 2 30 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 280 (accept_3_3 59 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 280 2 29 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 280 2 28 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 280 2 27 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 280 (accept_3_3 53 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 280 2 26 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 280 2 25 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 280 2 24 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 280 (accept_3_3 47 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 280 2 23 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 280 (Polychromatic418967fa.accept_19_7_11_14_1_11901 45 106 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 280 2 22 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 280 2 21 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 280 (accept_3_3 41 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 280 2 20 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 280 2 19 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 280 2 18 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 280 (accept_3_3 35 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 280 2 17 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 280 2 16 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 280 2 15 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 280 (accept_3_3 29 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 280 2 14 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 280 (Polychromatic418967fa.accept_21_6_1_7_1_11405 27 106 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 280 2 13 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 280 2 12 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 280 (accept_3_3 23 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 280 2 11 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 280 2 10 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 280 2 9 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 106 280 (accept_3_3 17 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 106 280 2 8 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 106 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 280 2 7 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 280 2 6 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 106 280 (accept_3_3 11 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 106 280 2 5 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 106 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 106 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 280 2 4 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 280 2 3 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 280 (accept_3_3 5 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  280 2 2 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 106 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 280 2 1 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 106 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 106 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 105 280 (allA_succ_of_accept 104 105 280 (accept_3_3 104 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 105 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 105 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 102 105
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 105 280 (accept_3_3 101 105
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 105 280 5 20 21 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 105 280
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 99 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 105 280 7 14 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 105 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 105 280
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 96 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 95 105 280 5 19 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 94 105 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 94 105 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 105 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 93 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 105 280 (accept_3_3 92 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91
  105 280 7 13 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  90 105 280 5 18 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 105 280 (accept_3_3 89 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 105 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 105 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 87 105 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 105 280 (accept_3_3 86 105 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 105 280 5 17 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 105 280 7 12 15 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 280 (accept_3_3 83 105 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 280 (Polychromatic418967fa.accept_19_6_10_14_1_3542 82 105
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 105 280
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 105 280 5 16 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 105 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 105 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  78 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 105 280 7 11 15 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 105 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 76 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 280 5 15 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 280 (accept_3_3 74 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 105 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 280 (Polychromatic418967fa.accept_19_15_10_14_1_3652 72
  105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 280 (accept_3_3 71
  105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 280 35 2 3 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 105 280
  (Polychromatic418967fa.accept_19_12_10_14_1_6353 69 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 105 280 (accept_3_3 68 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 105 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 105 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 105 280 5 13 21 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 280
  (Polychromatic418967fa.accept_17_13_3_8_1_6310 64 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 105 280 7 9 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 105 280 (accept_3_3 62 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 105 280 5 12 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 105 280 (accept_3_3 59 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 105 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 105 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 105 280 7 8 15 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 105 280 5 11 21 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 105 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 280 (accept_3_3 53 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 280 (Polychromatic418967fa.accept_24_3_9_16_1_8812 51 105 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 105 280 5 10 21 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 105 280 7 7 15 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 105 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 280 (accept_3_3 47 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 280 (Polychromatic418967fa.accept_17_12_3_8_1_7627 46 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 105 280 5 9 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 105 280 (accept_3_3 44 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 105 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 280 7 6 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 280 (accept_3_3 41 105 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 280 5 8 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 105 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 280 (accept_3_3 38 105 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37
  105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 280
  (Polychromatic418967fa.accept_16_4_9_8_1_2509 36 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 105 280 35 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 105 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 105 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 280 (Polychromatic418967fa.accept_16_1_9_8_1_2438 33 105
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 280 (accept_3_3 32 105
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 280 5 6 21 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 280
  (accept_3_3 29 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 105 280 7 4 15 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 105 280
  (Polychromatic418967fa.accept_18_9_15_10_1_395 27 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 280 (accept_3_3 26 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  105 280 5 5 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 105 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 280 (accept_3_3 23 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 105 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 280 7 3 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 105 280 5 4 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 280 (accept_3_3 17 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 105 280 5 3 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 105 280 7 2 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 280 (accept_3_3 11 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  105 280 5 2 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 105 280 (Polychromatic418967fa.accept_18_9_15_10_1_395 9 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 280 (accept_3_3 8 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 105 280 7 1 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 105 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 105 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 280 5 1 21 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 105 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 280 (accept_3_3 2 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 104 280 (allA_of_3_1 104 104 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 103 280
  (allA_succ_of_accept 102 103 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 102 103 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 103 280 (accept_3_3 101 103 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 103 280 (Polychromatic418967fa.accept_16_4_7_8_1_5753 100 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 99 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 103 280 (accept_3_3 98 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 97 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 103 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 96 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 103 280 (accept_3_3 95 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 103 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 94 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 93 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 103 280 (accept_3_3 92 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 103 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 91 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 103 280 (Polychromatic418967fa.accept_24_18_7_16_1_15629 90 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 280 (accept_3_3 89 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 103 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 87 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 280 (accept_3_3 86 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 280 (Polychromatic418967fa.accept_19_9_8_14_1_10621 85 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 280 (accept_3_3 83 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 280 (accept_3_3 80 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 280 (accept_3_3 77 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 76 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 280 (accept_3_3 74 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 280 (Polychromatic418967fa.accept_13_8_12_7_1_2442 73 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 72 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 280 (accept_3_3 71 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 103 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 280 (accept_3_3 68 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 280 (Polychromatic418967fa.accept_21_4_19_7_1_5142 67 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 280 (accept_3_3 65 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 64 103 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 280 (accept_3_3 62 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 280 (accept_3_3 59 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 280 (accept_3_3 56 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 280 (Polychromatic418967fa.accept_17_4_1_8_1_5070 55 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 280 (accept_3_3 53 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 103 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 280 (accept_3_3 50 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079 49 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 280 (accept_3_3 47 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 280 (accept_3_3 44 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 280 (accept_3_3 41 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 280 (Polychromatic418967fa.accept_18_4_13_10_1_2064 40 103 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 280 (accept_3_3 38 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 280 (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 280 (accept_3_3 35 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 103 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 280 (accept_3_3 32 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 280 (accept_3_3 29 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 280 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 103 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 280 (accept_3_3 26 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 280 (accept_3_3 23 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 280 (accept_3_3 20 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 280 (accept_3_3 17 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 103 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 280 (accept_3_3 14 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 280 (Polychromatic418967fa.accept_19_13_8_14_1_4960 13 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 280 (accept_3_3 11 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 280 (accept_3_3 8 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 280 (accept_3_3 5 103 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 280 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 103 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 280 (accept_3_3 2 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 103 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  102 280 (allA_succ_of_accept 101 102 280 (accept_3_3 101 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 102 280 2 50 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 102 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 99 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 102 280 2 49 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 102 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 97 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 102 280 2 48 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 102 280 (accept_3_3 95 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 102 280 2 47 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 102 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 93 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 102 280 2 46 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 280
  (Polychromatic418967fa.accept_19_15_7_14_1_11879 91 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 102 280 2 45 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 102 280 (accept_3_3 89 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 102 280 2 44 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 102 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 102 280 2 43 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 85 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 280 2 42 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 280 (accept_3_3 83 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 102 280 2 41 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 102 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 102 280 2 40 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 79 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 280 2 39 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 280 (accept_3_3 77 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 102 280 2 38 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 102 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 102 280 2 37 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 280
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 73 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 102 280 2 36 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 102 280 (accept_3_3 71 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 102 280 2 35 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 102 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 280 2 34 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 280 2 33 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 280 (accept_3_3 65 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 102 280 2 32 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 102 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 280 2 31 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 280 2 30 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 280 (accept_3_3 59 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 280 2 29 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 280 2 28 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 280
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 280 2 27 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 280 (accept_3_3 53 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 280 2 26 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 280 2 25 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 280 2 24 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 280 (accept_3_3 47 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 280 2 23 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 280 2 22 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 280 2 21 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 280 (accept_3_3 41 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 280 2 20 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 280 2 19 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 280
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 37 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 102 280 2 18 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 102 280 (accept_3_3 35 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 280 2 17 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 280 2 16 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 280 2 15 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 280 (accept_3_3 29 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 280 2 14 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 280 2 13 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 280 2 12 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 280 (accept_3_3 23 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 280 2 11 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 280 2 10 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 280 2 9 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 102 280 (accept_3_3 17 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 102 280 2 8 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 102 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 280 2 7 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 280 2 6 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 102 280 (accept_3_3 11 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 280 2 5 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 102 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 102 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 280 2 4 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 280 2 3 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 280 (accept_3_3 5 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102
  280 2 2 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  102 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 102 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 102 280 2 1 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 102 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 102 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  101 280 (allA_of_3_1 101 101 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 100 280 (allA_succ_of_accept 99
  100 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 99 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 100 280 2 49 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 100 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 97 100 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 100 280 4 24 25 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 95 100 280 5 19 20 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 94 100 280 2 47 50 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 100 280
  (Polychromatic418967fa.accept_13_2_9_7_1_164 93 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 100 280 4 23 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 100 280 (Polychromatic418967fa.accept_16_11_4_8_1_3435 91 100 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 100 280 10 9 10 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 100 280 (accept_3_3 89 100 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 100 280 4 22 25 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 100 280
  (Polychromatic418967fa.accept_16_7_4_8_1_2487 87 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 100 280 2 43 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 100 280 5 17 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 100 280 4 21 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 100 280 (accept_3_3 83 100 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 100 280 2 41 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 100 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 81 100 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 280 20 4 5 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 280
  (Polychromatic418967fa.accept_16_15_4_8_1_1562 79 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 100 280 2 39 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 280 (accept_3_3 77 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 280 4 19 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 100 280 5 15 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 100 280 2 37 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 73 100 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 100 280 4 18 25 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 100 280 (accept_3_3 71
  100 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 100 280 10 7 10 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 100 280
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 69 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 100 280 4 17 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 100 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 67 100 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 100 280 2 33 50 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 100 280 5 13 20 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 100 280 4 16 25 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 100 280
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 100 280 2 31 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 100 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 61 100 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 100 280 20 3 5 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 100 280 (accept_3_3 59 100 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 100 280 2 29 50 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 100 280
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 57 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 100 280 4 14 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 100 280 5 11 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 100 280 2 27 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 100 280 (accept_3_3 53 100 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 100 280 4 13 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 100 280 (Polychromatic418967fa.accept_16_3_4_8_1_3450 51 100 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 280 10 5 10 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 49 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 280 4 12 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 280 (accept_3_3 47 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 280 2 23 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 100 280 5 9 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 100 280 4 11 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 100 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 100 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 100 280 2 21 50 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 100 280 (accept_3_3 41 100 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 100 280 20 2 5 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 100 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 100 280 2 19 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 100 280 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 100 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 100 280 4 9 25 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 100 280 5 7 20 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 100 280 2 17 50 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 100 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 33 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 100 280 4 8 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 100 280 (Polychromatic418967fa.accept_16_15_4_8_1_1562 31 100 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 280 10 3 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 280 (accept_3_3 29 100 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 280 4 7 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 280 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 100
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 280 2 13 50 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 100 280 5 5 20 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 100 280 4 6 25 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 280 (accept_3_3 23
  100 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 280 2 11 50 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 280
  (Polychromatic418967fa.accept_13_8_9_7_1_530 21 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 280 20 1 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 100 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 100 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 280 2 9 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 280 (accept_3_3 17 100 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 280 4 4 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 100 280 5 3 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 100 280 2 7 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 280 (Polychromatic418967fa.accept_16_13_4_8_1_4557
  13 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 280 4 3 25 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 280
  (accept_3_3 11 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 280 10 1 10 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 280
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 280 4 2 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 280 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7 100 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 280 2 3 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 100 280 5 1 20 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 100 280 4 1 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 100 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3
  100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 280 2 1 50 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 100 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 99 280 (allA_succ_of_accept 98 99 280 (accept_3_3 98 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 99 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 99 280 (Polychromatic418967fa.accept_17_11_14_8_1_2729 96 99
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 99 280 (accept_3_3 95 99 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135
  94 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 99 280
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 93 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 99 280 (accept_3_3 92 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 99 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 90 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 99 280 (accept_3_3 89 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074 88 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 99 280
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 87 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 99 280 (accept_3_3 86 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 99 280 (Polychromatic418967fa.accept_16_4_3_8_1_2486 84 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 99 280 (accept_3_3 83 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 280 (Polychromatic418967fa.accept_21_19_15_7_1_3709 82 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 99 280
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 81 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 99 280 (accept_3_3 80 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 99 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 78 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 280 (accept_3_3 77 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 76 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 99 280
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 75 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 99 280 (accept_3_3 74 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 99 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326 72 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 280 (accept_3_3 71 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 280 (Polychromatic418967fa.accept_19_13_4_14_1_11912 70 99
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 99 280
  (Polychromatic418967fa.accept_16_5_3_8_1_4555 69 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 99 280 (accept_3_3 68 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 99 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 66 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 280 (accept_3_3 65 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 280 (Polychromatic418967fa.accept_13_12_8_7_1_2526 64 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 280
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 63 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 280 (accept_3_3 62 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 280 (Polychromatic418967fa.accept_16_12_3_8_1_5729 60 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 280 (accept_3_3 59 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 280 (Polychromatic418967fa.accept_17_7_14_8_1_5069 58 99
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 57 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 280 (accept_3_3 56 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 280 (accept_3_3 53 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 280 (Polychromatic418967fa.accept_16_4_3_8_1_2486 52 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 280
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 280 (accept_3_3 50 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 48 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 280 (accept_3_3 47 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 46 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 280
  (Polychromatic418967fa.accept_16_13_3_8_1_2422 45 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 280 (accept_3_3 44 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 280 (accept_3_3 41 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 40 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 280
  (Polychromatic418967fa.accept_21_18_15_7_1_9864 39 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 280 (accept_3_3 38 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 280 (accept_3_3 35 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 34 99
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 280
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 280 (accept_3_3 32 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 280 (accept_3_3 29 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 280 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 280
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 280 (accept_3_3 26 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 280 (Polychromatic418967fa.accept_17_7_14_8_1_5069 24 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 280 (accept_3_3 23 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 22 99 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 280
  (Polychromatic418967fa.accept_16_5_3_8_1_4555 21 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 280 (accept_3_3 20 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 280 (accept_3_3 17 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 280
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 15 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 280 (accept_3_3 14 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 280 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 280 (accept_3_3 11 99 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 99
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 280
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 280 (accept_3_3 8 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 99 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 280 (accept_3_3 5 99 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 99 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3
  99 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 280 (accept_3_3 2 99 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  280 (allA_of_3_1 98 98 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 97 280 (allA_succ_of_accept 96 97 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 96 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 97 280 (accept_3_3 95 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94
  97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 94 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 280 (accept_3_3 92 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 91 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 280
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 90 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 280 (accept_3_3 89 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 280 (Polychromatic418967fa.accept_17_3_12_8_1_1688 88 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 280 (accept_3_3 86 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 280 (accept_3_3 83 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 280 (accept_3_3 80 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 79 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 280 (accept_3_3 77 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 280 (accept_3_3 74 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 73 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 280
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 72 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 280 (accept_3_3 71 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 280 (accept_3_3 68 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 280 (accept_3_3 65 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 280 (Polychromatic418967fa.accept_13_12_6_7_1_1071 64 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 280 (accept_3_3 62 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 280 (Polychromatic418967fa.accept_13_9_6_7_1_551 61 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 280 (accept_3_3 59 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 280 (accept_3_3 56 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 280 (Polychromatic418967fa.accept_16_7_1_8_1_5796 55 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 280
  (Polychromatic418967fa.accept_17_3_12_8_1_1688 54 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 280 (accept_3_3 53 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 280 (Polychromatic418967fa.accept_16_4_1_8_1_835 52 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 280 (accept_3_3 50 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 280 (accept_3_3 47 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 280 (accept_3_3 44 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 280 (Polychromatic418967fa.accept_13_4_6_7_1_2471 43 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 280 (accept_3_3 41 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 280 (accept_3_3 38 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 280 (Polychromatic418967fa.accept_17_3_12_8_1_1688 37 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 280
  (Polychromatic418967fa.accept_16_4_1_8_1_835 36 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 280 (accept_3_3 35 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 280 (accept_3_3 32 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 280 (accept_3_3 29 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 280 (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 280 (accept_3_3 26 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 280 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 280 (accept_3_3 23 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 280 (accept_3_3 20 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 280
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 280 (accept_3_3 17 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 280 (accept_3_3 14 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 280 (accept_3_3 11 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 280 (accept_3_3 8 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 97 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 280 (accept_3_3 5 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 97 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 280 (accept_3_3 2 97 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 97 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 280
  (allA_succ_of_accept 95 96 280 (accept_3_3 95 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 96
  280 2 47 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  93 96 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 92 96 280 4 23 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 96 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 91 96 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 280 2 45 48 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 280 (accept_3_3 89 96 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 96 280 8 11 12 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 96 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 87 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 96 280 2 43 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 96 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 96 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 280 4 21 24 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 280 (accept_3_3 83 96 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 96 280 2 41 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 96 280 (Polychromatic418967fa.accept_21_18_12_7_1_6712
  81 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 280 8 10 12 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 79 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 280 2 39 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 96 280 (accept_3_3 77 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 96 280 4 19 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 96 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 96 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 96 280 2 37 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 96 280 (Polychromatic418967fa.accept_22_7_8_16_1_17188
  73 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 280 8 9 12 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 280 (accept_3_3 71
  96 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 280 2 35 48 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 69 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 280 4 17 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 96 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 280 2 33 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 280 (accept_3_3 65 96 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 280 8 8 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 96 280 (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 96 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 280 2 31 48 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 280 4 15 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 280 (accept_3_3 59 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96
  280 2 29 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  57 96 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 96 280 8 7 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 96 280 (Polychromatic418967fa.accept_19_17_1_14_1_6360 55 96 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 280 2 27 48 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 280 (accept_3_3 53 96 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 280 4 13 24 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 280
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 280 2 25 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 96 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 96 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 280 8 6 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 280 (accept_3_3 47 96 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 280 2 23 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 280 (Polychromatic418967fa.accept_21_3_12_7_1_3755 45 96 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 280 4 11 24 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 280 2 21 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 96 280 (accept_3_3 41 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 280 8 5 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 96 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 96 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 280 2 19 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 280 (Polychromatic418967fa.accept_13_11_5_7_1_2420
  37 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 280 4 9 24 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 280 (accept_3_3 35
  96 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 280 2 17 48 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 280
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 280 8 4 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 96 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 280 2 15 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 280 (accept_3_3 29 96 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 280 4 7 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 96 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 96 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 280 2 13 48 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 280 8 3 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 280 (accept_3_3 23 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  280 2 11 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 96 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 280 4 5 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 280 (Polychromatic418967fa.accept_15_4_6_10_1_823 19 96 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 280 2 9 48 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 280 (accept_3_3 17 96 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 280 8 2 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 96 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 280 2 7 48 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 280 4 3 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 280 (accept_3_3 11 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  280 2 5 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 280 (Polychromatic418967fa.accept_17_9_11_8_1_5077 9 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 280 8 1 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 280 2 3 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 280 (accept_3_3 5 96 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 280 4 1 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 280 2 1 48 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 280
  (Polychromatic418967fa.accept_15_1_6_10_1_23 1 96 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 95 280 (allA_of_3_1 95 95 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 94 280
  (allA_succ_of_accept 93 94 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 93 94 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 94 280 2 46 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 94 280 (Polychromatic418967fa.accept_12_7_10_4_1_382
  91 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 94 280 2 45 47 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 94 280
  (accept_3_3 89 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 94 280 2 44 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 94 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 87 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 94 280 2 43 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 94 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 85 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 94 280 2 42 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 94 280 (accept_3_3 83 94 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 94 280 2 41 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 94 280 (Polychromatic418967fa.accept_15_6_4_10_1_2319
  81 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 280 2 40 47 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 79 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 94 280 2 39 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 94 280 (accept_3_3 77 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 94 280 2 38 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 94 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 94 280 2 37 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 94 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 94 280 2 36 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 94 280 (accept_3_3 71 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 94 280 2 35 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 94 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 280 2 34 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 280
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 67 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 280 2 33 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 94 280 (accept_3_3 65 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 94 280 2 32 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 94 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 94 280 2 31 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 94 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 94 280 2 30 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 94 280 (accept_3_3 59 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 94 280 2 29 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 94 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 280 2 28 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 280 2 27 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 94 280 (accept_3_3 53 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 94 280 2 26 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 94 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 280 2 25 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 280 2 24 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 94 280 (accept_3_3 47 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 94 280 2 23 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 94 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 94 280 2 22 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 94 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 94 280 2 21 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 94 280 (accept_3_3 41 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 94 280 2 20 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 280 2 19 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 280 2 18 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 94 280 (accept_3_3 35 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 94 280 2 17 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 94 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 280 2 16 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 280 2 15 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 94 280 (accept_3_3 29 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 94 280 2 14 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 94 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 94 280 2 13 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 94 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 94 280 2 12 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 94 280 (accept_3_3 23 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 94 280 2 11 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 94 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 280 2 10 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 280 2 9 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 280 (accept_3_3 17 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  280 2 8 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 280 2 7 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 94 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 94 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 280 2 6 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 280 (accept_3_3 11 94 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 280 2 5 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 280
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 280 2 4 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 94 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 280 2 3 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 280 (accept_3_3 5 94 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 280 2 2 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 94 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 280 2 1 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1
  94 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 280
  (allA_succ_of_accept 92 93 280 (accept_3_3 92 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 93 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 90 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 93 280 (accept_3_3 89 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 93 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 87 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 93 280 (accept_3_3 86 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 93 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 84 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 93 280 (accept_3_3 83 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 280 (Polychromatic418967fa.accept_15_7_3_10_1_817 82 93 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 93 280
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 81 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 93 280 (accept_3_3 80 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 280 (accept_3_3 77 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 280
  (Polychromatic418967fa.accept_16_11_13_8_1_1578 75 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 280 (accept_3_3 74 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 280 (Polychromatic418967fa.accept_19_15_17_14_1_1370 72 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 280 (accept_3_3 71 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 93 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 69 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 280 (accept_3_3 68 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 280 (accept_3_3 65 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 280 (Polychromatic418967fa.accept_22_20_5_16_1_14148 64 93 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 280
  (Polychromatic418967fa.accept_24_15_21_16_1_12209 63 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 93 280 (accept_3_3 62 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 93 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 280 (accept_3_3 59 93 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 58
  93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 280
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 57 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 280 (accept_3_3 56 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 280 (accept_3_3 53 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 280 (accept_3_3 50 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 280 (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 280 (accept_3_3 47 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 280 (Polychromatic418967fa.accept_24_22_21_16_1_15626 46 93 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 280
  (Polychromatic418967fa.accept_21_3_9_7_1_8369 45 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 280 (accept_3_3 44 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 280 (accept_3_3 41 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 280
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 280 (accept_3_3 38 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 280 (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 280 (accept_3_3 35 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 93 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 280 (accept_3_3 32 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 280 (accept_3_3 29 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 280 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 280
  (Polychromatic418967fa.accept_16_11_13_8_1_1578 27 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 280 (accept_3_3 26 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 280 (accept_3_3 23 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 280
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 280 (accept_3_3 20 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 280 (accept_3_3 17 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 280 (accept_3_3 14 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 280 (Polychromatic418967fa.accept_16_12_13_8_1_2409 12 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 280 (accept_3_3 11 93 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 280 (Polychromatic418967fa.accept_21_10_9_7_1_9857 10 93
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 280
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 280 (accept_3_3 8 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 93 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 280 (accept_3_3 5 93 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 93 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 280 (Polychromatic418967fa.accept_16_3_13_8_1_1594
  3 93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 280 (accept_3_3 2 93
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  93 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 280
  (allA_of_3_1 92 92 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 91 280 (allA_succ_of_accept 90 91 280
  (Polychromatic418967fa.accept_22_2_3_16_1_15735 90 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 91 280 (accept_3_3 89 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  91 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 88 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 91 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 91 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 280 (accept_3_3 86 91 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 85 91 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 91 280 7 12 13 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 91 280 (accept_3_3 83 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 91 280 (Polychromatic418967fa.accept_12_10_7_4_1_820
  82 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 91 280 (accept_3_3 80 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  91 280 (Polychromatic418967fa.accept_22_13_3_16_1_17187 79 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 91 280 (Polychromatic418967fa.accept_25_3_16_5_1_15548 78 91 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 91 280 7 11 13 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 91 280
  (Polychromatic418967fa.accept_16_12_11_8_1_832 76 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 91 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 280 (accept_3_3 74 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 91 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 73 91 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 280
  (Polychromatic418967fa.accept_23_3_22_4_1_17186 72 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 280 (accept_3_3 71 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 91
  280 7 10 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  91 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 91 280 (accept_3_3 68 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 91 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 67 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 280 (Polychromatic418967fa.accept_15_6_1_10_1_1549 66 91
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 280 (accept_3_3 65 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 280
  (Polychromatic418967fa.accept_19_7_15_14_1_3659 64 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 91 280 7 9 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 91 280 (accept_3_3 62 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 280 (Polychromatic418967fa.accept_16_13_11_8_1_2449 61 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 280 (Polychromatic418967fa.accept_16_12_11_8_1_832 60 91 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 280 (accept_3_3 59 91 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 91 280 7 8 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 91 280 (Polychromatic418967fa.accept_19_17_15_14_1_3623 55 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 91
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 280 (accept_3_3 53 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 280 (Polychromatic418967fa.accept_11_8_3_5_1_355
  52 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 280 (accept_3_3 50 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 91
  280 7 7 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  91 280 (Polychromatic418967fa.accept_17_14_6_8_1_7688 48 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 91 280 (accept_3_3 47 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 91 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 280 (accept_3_3 44 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 280 (Polychromatic418967fa.accept_15_13_1_10_1_816
  43 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 91 280 7 6 13 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 91 280 (accept_3_3 41
  91 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 280
  (Polychromatic418967fa.accept_25_15_16_5_1_17185 40 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 280 (accept_3_3 38 91 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 91 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 280
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 91 280 7 5 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 91 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 280 (accept_3_3 32 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 280 (Polychromatic418967fa.accept_17_14_6_8_1_7688
  31 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 30 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 280 (accept_3_3 29 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91
  280 7 4 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  91 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 91 280 (accept_3_3 26 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 91 280 (Polychromatic418967fa.accept_24_1_19_16_1_17184 25 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 24 91
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 280 (accept_3_3 23 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 280 (Polychromatic418967fa.accept_12_10_7_4_1_820
  22 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 91 280 7 3 13 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 91 280 (accept_3_3 20
  91 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 91 280 (Polychromatic418967fa.accept_19_18_15_14_1_5017 18 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 280 (accept_3_3 17 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 91 280 (Polychromatic418967fa.accept_18_16_1_10_1_2029 16 91 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 91 280 7 2 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 91 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 280 (Polychromatic418967fa.accept_16_12_11_8_1_832 12 91
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 280 (accept_3_3 11 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 280 (Polychromatic418967fa.accept_12_10_7_4_1_820
  10 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 280 (accept_3_3 8 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 280
  7 1 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 91
  280 (Polychromatic418967fa.accept_15_6_1_10_1_1549 6 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 91 280 (accept_3_3 5 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 91 280 (Polychromatic418967fa.accept_16_4_11_8_1_1574 4 91 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 280 (accept_3_3 2 91 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 280 (Polychromatic418967fa.accept_19_1_15_14_1_5032
  1 91 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 280
  (allA_succ_of_accept 89 90 280 (accept_3_3 89 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 90
  280 2 44 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  87 90 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 87 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 90 280 2 43 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 85 90 280 5 17 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 90 280 2 42 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 280 (accept_3_3 83 90 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 90 280 2 41 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 90 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 90 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 90 280 10 8 9 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 280
  (Polychromatic418967fa.accept_21_16_6_7_1_6764 79 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 280 2 39 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 90 280 (accept_3_3 77 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 90 280 2 38 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 90 280 5 15 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 90 280 2 37 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 90 280 (Polychromatic418967fa.accept_13_8_12_7_1_2442 73 90 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 280 2 36 45 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 280 (accept_3_3 71 90 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 280 10 7 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 69
  90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 280 2 34 45 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 280
  (Polychromatic418967fa.accept_21_4_6_7_1_3693 67 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 280 2 33 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 90 280 5 13 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 90 280 2 32 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 90 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 90 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 280 2 31 45 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 280
  (Polychromatic418967fa.accept_23_15_21_4_1_12474 61 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 90 280 10 6 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 90 280 (accept_3_3 59 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 90 280 2 29 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 90 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 90 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 280 2 28 45 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 90 280 5 11 18 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 280 2 27 45 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 280 (accept_3_3 53 90 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 280 2 26 45 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 280 10 5 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079 49 90 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 280 2 24 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 280 (accept_3_3 47 90 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 280 2 23 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 280 5 9 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 280 2 22 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 280 (Polychromatic418967fa.accept_13_4_12_7_1_2439
  43 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 280 2 21 45 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 280
  (accept_3_3 41 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 280 10 4 9 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 39 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 280 2 19 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 90 280 (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 90 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 280 2 18 45 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 280 5 7 18 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 280 2 17 45 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 280 2 16 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 90 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 90 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 280 10 3 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 280 (accept_3_3 29 90 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 280 2 14 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 90 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 280 2 13 45 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 280 5 5 18 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 280 2 12 45 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 280
  (accept_3_3 23 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 280 2 11 45 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 280 10 2 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 90 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 280 2 9 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 280 (accept_3_3 17 90 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 280 2 8 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 280 5 3 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 280 2 7 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 280 (Polychromatic418967fa.accept_17_13_5_8_1_896 13 90 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 280 2 6 45 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 280 (accept_3_3 11
  90 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 280 10 1 9 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 280 2 4 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 280 (Polychromatic418967fa.accept_24_7_18_16_1_12162 7 90 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 280 2 3 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 280 5 1 18 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 280 2 2 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 90 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 280 2 1 45 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 280
  (Polychromatic418967fa.accept_21_1_6_7_1_17183 1 90 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 280 (allA_of_3_1 89 89 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 280 (allA_succ_of_accept 87 88
  280 (Polychromatic418967fa.accept_9_6_7_1_1_145 87 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 88 280 2 43 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 88 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 88 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 88 280 4 21 22 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 88 280 (accept_3_3 83 88 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88 280 2 41 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 88 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  81 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 88 280 8 10 11 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 88 280
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 79 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 88 280 2 39 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 88 280 (accept_3_3 77 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 88 280 4 19 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 88 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 88 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 88 280 2 37 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 88 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702
  73 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 88 280 8 9 11 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 88 280 (accept_3_3 71
  88 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88 280 2 35 44 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 88 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 69 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 88 280 4 17 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 88 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 88 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 88 280 2 33 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 88 280 (accept_3_3 65 88 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88 280 8 8 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 88 280 (Polychromatic418967fa.accept_15_3_13_10_1_2332 63 88 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 280 2 31 44 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 280
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 61 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 88 280 4 15 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 88 280 (accept_3_3 59 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88
  280 2 29 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  57 88 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 88 280 8 7 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 88 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 55 88 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 88 280 2 27 44 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 88 280 (accept_3_3 53 88 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88 280 4 13 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 88 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51
  88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 280 2 25 44 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 88 280 8 6 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 88 280 (accept_3_3 47 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88
  280 2 23 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 88 280 (Polychromatic418967fa.accept_19_7_12_14_1_9206 45 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 88 280 4 11 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 88 280 (Polychromatic418967fa.accept_13_4_10_7_1_1701 43 88 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 280 2 21 44 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 280 (accept_3_3 41 88 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 280 8 5 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 39
  88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 280 2 19 44 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 280
  (Polychromatic418967fa.accept_18_1_16_10_1_2065 37 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 280 4 9 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 280 (accept_3_3 35 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  280 2 17 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 88 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 280 8 4 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 88 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 88 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 280 2 15 44 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 280 (accept_3_3 29 88 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 280 4 7 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 88
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 280 2 13 44 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 280
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 280 8 3 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 280 (accept_3_3 23 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  280 2 11 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 88 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 280 4 5 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 88 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 88 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 280 2 9 44 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 280 (accept_3_3 17 88 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 280 8 2 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 88 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15
  88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 280 2 7 44 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 280 4 3 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 280 (accept_3_3 11 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  280 2 5 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 280 (Polychromatic418967fa.accept_19_9_12_14_1_4966 9 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 280 8 1 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 280 (Polychromatic418967fa.accept_19_7_12_14_1_9206 7 88 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 280 2 3 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 280 (accept_3_3 5 88 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 280 4 1 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 88 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 280 2 1 44 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 280
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 88 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87
  280 (allA_succ_of_accept 86 87 280 (accept_3_3 86 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 84 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 280 (accept_3_3 83 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 82 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 280 (accept_3_3 80 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 78 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 280 (accept_3_3 77 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 75 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 280 (accept_3_3 74 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 280 (accept_3_3 71 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 280
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 69 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 280 (accept_3_3 68 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 280 (accept_3_3 65 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 280 (Polychromatic418967fa.accept_19_7_11_14_1_11901 64 87 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 280
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 280 (accept_3_3 62 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 60 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 280 (accept_3_3 59 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 280 (accept_3_3 56 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 280 (accept_3_3 53 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 280
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 51 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 280 (accept_3_3 50 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 280 (accept_3_3 47 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 280 (Polychromatic418967fa.accept_21_4_3_7_1_11420 46 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 280
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 280 (accept_3_3 44 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 280 (accept_3_3 41 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 280 (accept_3_3 38 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 280 (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 280 (accept_3_3 35 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 87 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 280
  (Polychromatic418967fa.accept_16_1_7_8_1_3422 33 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 280 (accept_3_3 32 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 280 (accept_3_3 29 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 280
  (Polychromatic418967fa.accept_17_10_2_8_1_6295 27 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 280 (accept_3_3 26 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 280 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 280 (accept_3_3 23 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 87 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 280 (accept_3_3 20 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 280 (accept_3_3 17 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 280 (accept_3_3 14 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 280 (accept_3_3 11 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 280 (Polychromatic418967fa.accept_17_10_2_8_1_6295 10 87 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 280 (accept_3_3 8 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 87 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 280 (accept_3_3 5 87 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 87 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 280 (accept_3_3 2 87 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 280
  (allA_of_3_1 86 86 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 280 (allA_succ_of_accept 84 85 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 280 (accept_3_3 83 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 85 280 5 16 17 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 85 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 79 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 280 (accept_3_3 77 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 280 (Polychromatic418967fa.accept_16_12_5_8_1_2492 76 85 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 85 280 5 15 17 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 85 280 (accept_3_3 74 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 280
  (Polychromatic418967fa.accept_18_1_13_10_1_2024 73 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 280 (Polychromatic418967fa.accept_25_22_10_5_1_17182 72 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 280 (accept_3_3 71 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 85 280 5 14 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 85 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 280 (accept_3_3 68 85 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 280 (Polychromatic418967fa.accept_16_3_5_8_1_4543 67 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 85 280 5 13 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 85 280 (Polychromatic418967fa.accept_26_12_7_20_1_17181 64 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 280 (accept_3_3 62 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61
  85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 280 5 12 17 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 280 (accept_3_3 59
  85 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 58 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 85 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 280 (accept_3_3 56 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 85 280 5 11 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 85 280 (Polychromatic418967fa.accept_19_16_9_14_1_10638 54 85 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 280 (accept_3_3 53 85 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 85 280 5 10 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 85 280 (Polychromatic418967fa.accept_19_11_9_14_1_6386 49 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 280 (accept_3_3 47 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219
  46 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 280 5 9 17 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 280 (accept_3_3 44
  85 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 85 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 280 (accept_3_3 41 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 85 280 5 8 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 85 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 85 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 280 (accept_3_3 38 85 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 280 (Polychromatic418967fa.accept_18_1_13_10_1_2024 37 85 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 85 280 5 7 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 85 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 280 (accept_3_3 32 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 280
  (Polychromatic418967fa.accept_19_12_9_14_1_6365 31 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 85 280 5 6 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 85 280 (accept_3_3 29 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 280 (Polychromatic418967fa.accept_16_12_5_8_1_2492 28 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 280 (accept_3_3 26 85 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85 280 5 5 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 85 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 85 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 280 (accept_3_3 23 85 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 85 280 5 4 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 85 280 (Polychromatic418967fa.accept_16_3_5_8_1_4543 19 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 280 (Polychromatic418967fa.accept_25_18_10_5_1_17180 18 85
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 280 (accept_3_3 17 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16
  85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 280 5 3 17 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 280 (accept_3_3 14
  85 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 280
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 85 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 280 (accept_3_3 11 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 85 280 5 2 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 85 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 280 (accept_3_3 8 85 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 85 280 5 1 17 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 85 280 (Polychromatic418967fa.accept_16_4_5_8_1_2425 4 85 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 280 (accept_3_3 2 85 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 280 (Polychromatic418967fa.accept_18_1_13_10_1_2024
  1 85 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 280
  (allA_succ_of_accept 83 84 280 (accept_3_3 83 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84
  280 2 41 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  81 84 280 (Polychromatic418967fa.accept_16_1_4_8_1_3434 81 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 84 280 4 20 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 84 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 84 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 280 2 39 42 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 84 280 7 11 12 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 84 280 4 19 21 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 75 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 280 2 37 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 84 280 (Polychromatic418967fa.accept_16_9_4_8_1_2533 73 84 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 280 4 18 21 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 280 (accept_3_3 71 84 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 280 14 5 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 84 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 280 4 17 21 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 67 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 280 2 33 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 84 280 (accept_3_3 65 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 280 4 16 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 84 280 7 9 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 84 280 2 31 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 84 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 84 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 280 4 15 21 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 280 (accept_3_3 59 84 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 280 2 29 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326
  57 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 280 28 2 3 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 280
  (Polychromatic418967fa.accept_16_7_4_8_1_2487 55 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 280 2 27 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 84 280 (accept_3_3 53 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 84 280 4 13 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 84 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 84 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 280 2 25 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 84 280 7 7 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 84 280 4 12 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 280 (accept_3_3 47 84 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 280 2 23 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 280 (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 84 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 280 4 11 21 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 280 14 3 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 280 (accept_3_3 41 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84
  280 4 10 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  84 280 (Polychromatic418967fa.accept_16_7_4_8_1_2487 39 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 84 280 2 19 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 84 280 (Polychromatic418967fa.accept_16_5_4_8_1_1560 37 84 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 280 4 9 21 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 280 7 5 12 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 84 280 2 17 42 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 280 4 8 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 280 2 15 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 280 (accept_3_3 29 84 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 280 28 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 84 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 84 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 280 2 13 42 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 280 4 6 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 280 (accept_3_3 23 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  280 2 11 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21
  84 280 7 3 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20
  84 280 4 5 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  19 84 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 19 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 84 280 2 9 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 84 280 (accept_3_3 17 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 84 280 4 4 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 84 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 280 14 1 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 280 4 3 21 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 280 (accept_3_3 11 84 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 280 2 5 42 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 280 4 2 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 84 280 7 1 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 84 280 2 3 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 280 (accept_3_3 5 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 280
  4 1 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84
  280 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 84 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 84 280 2 1 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 84 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 84 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 280 (allA_of_3_1
  83 83 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 280 (allA_succ_of_accept 81 82 280
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 81 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 280 2 40 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 82 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 79 82 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 280 2 39 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 280 (accept_3_3 77 82 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 280 2 38 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 280 (Polychromatic418967fa.accept_13_10_4_7_1_2465
  75 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 280 2 37 41 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 280 2 36 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 82 280 (accept_3_3 71 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 82 280 2 35 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 82 280 (Polychromatic418967fa.accept_19_12_6_14_1_15972 69 82 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 82 280 2 34 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 82 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 82 280 2 33 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 82 280 (accept_3_3 65 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 82 280 2 32 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 82 280 (Polychromatic418967fa.accept_13_11_4_7_1_2419 63 82 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 280 2 31 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 280 2 30 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 82 280 (accept_3_3 59 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 82 280 2 29 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 82 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 57 82 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 280 2 28 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 280 2 27 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 82 280 (accept_3_3 53 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 82 280 2 26 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 82 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 51 82 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 280 2 25 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 280 2 24 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 82 280 (accept_3_3 47 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 82 280 2 23 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 82 280 (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 82 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 280 2 22 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 280 2 21 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 82 280 (accept_3_3 41 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 82 280 2 20 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 82 280 (Polychromatic418967fa.accept_19_1_6_14_1_15982 39 82 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 280 2 19 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 280 2 18 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 82 280 (accept_3_3 35 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 82 280 2 17 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 82 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 33 82 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 280 2 16 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 280 2 15 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 82 280 (accept_3_3 29 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 82 280 2 14 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 82 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 82 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 280 2 13 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 280 2 12 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 82 280 (accept_3_3 23 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 82 280 2 11 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 82 280 (Polychromatic418967fa.accept_29_21_24_19_1_17179 21 82 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 280 2 10 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 280 2 9 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 280 (accept_3_3 17 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  280 2 8 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 280 (Polychromatic418967fa.accept_21_15_19_7_1_6741 15 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 280 2 7 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 82 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 82 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 280 2 6 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 280 (accept_3_3 11 82 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 280 2 5 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 280
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 280 2 4 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 82 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 280 2 3 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 280 (accept_3_3 5 82 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 280 2 2 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 82 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 280 2 1 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  82 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 280
  (allA_succ_of_accept 80 81 280 (accept_3_3 80 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 78 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 280 (accept_3_3 77 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 76 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 280
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 75 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 280 (accept_3_3 74 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 72 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 280 (accept_3_3 71 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 280 (Polychromatic418967fa.accept_19_13_5_14_1_3530 70 81
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 280
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 69 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 280 (accept_3_3 68 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 280 (accept_3_3 65 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 280 (Polychromatic418967fa.accept_15_4_6_10_1_823 64 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 280
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 280 (accept_3_3 62 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 280 (Polychromatic418967fa.accept_13_8_3_7_1_2455 60 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 280 (accept_3_3 59 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 280 (Polychromatic418967fa.accept_25_8_6_5_1_17178 58 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 57 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 280 (accept_3_3 56 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 280 (accept_3_3 53 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 280 (Polychromatic418967fa.accept_16_4_1_8_1_835 52 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 280
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 51 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 280 (accept_3_3 50 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 48 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 280 (accept_3_3 47 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 280
  (Polychromatic418967fa.accept_22_1_15_16_1_14154 45 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 280 (accept_3_3 44 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 81 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 81 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 280 (accept_3_3 41 81 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710
  40 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 280
  (Polychromatic418967fa.accept_16_7_1_8_1_5796 39 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 280 (accept_3_3 38 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 280 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 280 (accept_3_3 35 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 280 (Polychromatic418967fa.accept_13_8_3_7_1_2455 34 81 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 280
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 280 (accept_3_3 32 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 280 (accept_3_3 29 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 280 (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 280
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 280 (accept_3_3 26 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 280 (accept_3_3 23 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 22 81 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 280 (accept_3_3 20 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 280 (accept_3_3 17 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 16 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 280
  (Polychromatic418967fa.accept_16_15_1_8_1_1585 15 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 280 (accept_3_3 14 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 280 (accept_3_3 11 81 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 81 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 280
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 280 (accept_3_3 8 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 81 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 280 (accept_3_3 5 81 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 81 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539
  3 81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 280 (accept_3_3 2 81
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  81 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 280 (allA_of_3_1 80
  80 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 280 (allA_succ_of_accept 78 79 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 280 (accept_3_3 77 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 280 (accept_3_3 74 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 280 (Polychromatic418967fa.accept_13_8_1_7_1_2505 73 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 280
  (Polychromatic418967fa.accept_21_9_16_7_1_5222 72 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 280 (accept_3_3 71 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 280 (accept_3_3 68 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 280 (accept_3_3 65 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 280 (Polychromatic418967fa.accept_19_7_3_14_1_5023 64 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 280 (accept_3_3 62 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 280 (Polychromatic418967fa.accept_24_13_7_16_1_17177 61 79 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 280 (accept_3_3 59 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 280 (accept_3_3 56 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 55 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 280
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 54 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 280 (accept_3_3 53 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 280 (accept_3_3 50 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 280 (accept_3_3 47 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 280 (accept_3_3 44 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 280 (accept_3_3 41 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 280 (accept_3_3 38 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 280
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 280 (accept_3_3 35 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 280 (accept_3_3 32 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 280 (accept_3_3 29 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 280 (accept_3_3 26 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 280 (Polychromatic418967fa.accept_16_9_15_8_1_3425 25 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 280 (accept_3_3 23 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 280 (accept_3_3 20 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 280
  (Polychromatic418967fa.accept_17_1_11_8_1_2725 18 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 280 (accept_3_3 17 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 280 (accept_3_3 14 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 280 (accept_3_3 11 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 280 (accept_3_3 8 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 79 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 280 (accept_3_3 5 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 79 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 280 (accept_3_3 2 79 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 280 (Polychromatic418967fa.accept_16_1_15_8_1_2411 1 79 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 280
  (allA_succ_of_accept 77 78 280 (accept_3_3 77 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  280 2 38 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  75 78 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 280 2 37 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 280 (Polychromatic418967fa.accept_15_13_3_10_1_2296 73 78 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 280 2 36 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 280 (accept_3_3 71 78 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 280 2 35 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 69 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 280 2 34 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 78 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 78 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 280 2 33 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 280 (accept_3_3 65 78 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 280 2 32 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 63
  78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 280 2 31 39 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 280 2 30 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 78 280 (accept_3_3 59 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 78 280 2 29 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 78 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 78 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 280 2 28 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 280
  (Polychromatic418967fa.accept_19_17_2_14_1_11897 55 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 78 280 2 27 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 78 280 (accept_3_3 53 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 280 2 26 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 78 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 78 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 280 2 25 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 280 2 24 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 78 280 (accept_3_3 47 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 78 280 2 23 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 78 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 78 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 280 2 22 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 280 2 21 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 78 280 (accept_3_3 41 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 280 2 20 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 78 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 78 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 280 2 19 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 280
  (Polychromatic418967fa.accept_15_7_3_10_1_817 37 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 78 280 2 18 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 280 (accept_3_3 35 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 280 2 17 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 78 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 78 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 280 2 16 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 280 2 15 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 78 280 (accept_3_3 29 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 280 2 14 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 78 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 78 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 280 2 13 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 280 2 12 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 78 280 (accept_3_3 23 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 280 2 11 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 78 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 280 2 10 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 280
  (Polychromatic418967fa.accept_17_2_10_8_1_7691 19 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 78 280 2 9 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 78 280 (accept_3_3 17 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78
  280 2 8 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  78 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 78 280 2 7 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 78 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 78 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 280 2 6 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 280 (accept_3_3 11 78 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 280 2 5 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 280 2 4 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 280 2 3 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 280 (accept_3_3 5 78 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 280 2 2 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 78 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 280 2 1 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 280 (Polychromatic418967fa.accept_19_1_2_14_1_3666 1
  78 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 280 (allA_of_3_1 77 77
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 280 (allA_succ_of_accept 75 76 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 75 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 280 2 37 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 76 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 73 76 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 280 4 18 19 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 280 (accept_3_3 71 76 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 280 2 35 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 69
  76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 280 4 17 19 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 280
  (Polychromatic418967fa.accept_15_7_1_10_1_305 67 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 280 2 33 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 76 280 (accept_3_3 65 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 76 280 4 16 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 76 280 (Polychromatic418967fa.accept_16_15_12_8_1_4585 63 76 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 76 280 2 31 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 76 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61
  76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 280 4 15 19 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 280 (accept_3_3 59
  76 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 280 2 29 38 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 280 4 14 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 280 (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 76 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 280 2 27 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 280 (accept_3_3 53 76 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 280 4 13 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 76 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 280 2 25 38 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 280
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 49 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 280 4 12 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 280 (accept_3_3 47 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  280 2 23 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 76 280 (Polychromatic418967fa.accept_16_13_12_8_1_2451 45 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 280 4 11 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 76 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 280 2 21 38 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 280 (accept_3_3 41 76 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 280 4 10 19 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 280 2 19 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 76 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 76 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 280 4 9 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 280 (accept_3_3 35 76 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 280 2 17 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 76 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 280 4 8 19 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 280
  (Polychromatic418967fa.accept_13_5_11_7_1_559 31 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 280 2 15 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 76 280 (accept_3_3 29 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 76 280 4 7 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 76 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 76 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 280 2 13 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25
  76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 280 4 6 19 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 280 (accept_3_3 23
  76 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 280 2 11 38 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 76 280 4 5 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 76 280 (Polychromatic418967fa.accept_16_3_12_8_1_808 19 76 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 280 2 9 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 280 (accept_3_3 17 76 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 280 4 4 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 76 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 76 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 280 2 7 38 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 280
  (Polychromatic418967fa.accept_15_13_1_10_1_816 13 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 76 280 4 3 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 280 (accept_3_3 11 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76
  280 2 5 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  76 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 76 280 4 2 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 76 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 280 2 3 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 280 (accept_3_3 5 76 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 280 4 1 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 76 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 76 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 280 2 1 38 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 280
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 76 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 280
  (allA_succ_of_accept 74 75 280 (accept_3_3 74 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  75 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 75 280 (Polychromatic418967fa.accept_17_4_7_8_1_7491 72 75 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 280 (accept_3_3 71 75 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 75 280 5 14 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 75 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 280 (accept_3_3 68 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67
  75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 75 280 5 13 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 75 280 (Polychromatic418967fa.accept_13_12_10_7_1_2433 64 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 280 (Polychromatic418967fa.accept_23_17_6_4_1_17176 63 75
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 280 (accept_3_3 62 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61
  75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 280 5 12 15 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 280 (accept_3_3 59
  75 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 58 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 280 (Polychromatic418967fa.accept_21_15_12_7_1_5204 57 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 280 (accept_3_3 56 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 75 280 5 11 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 75 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 75 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 280 (accept_3_3 53 75 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 75 280 5 10 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 75 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 280 (Polychromatic418967fa.accept_17_14_7_8_1_7544 48 75
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 280 (accept_3_3 47 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 280 (Polychromatic418967fa.accept_21_4_12_7_1_5174
  46 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 280 5 9 15 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 280 (accept_3_3 44
  75 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 280 (accept_3_3 41 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 75 280 5 8 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 75 280 (Polychromatic418967fa.accept_19_1_18_14_1_6392 39 75 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 280 (accept_3_3 38 75 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 280
  (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 75 280 5 7 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 280 (accept_3_3 32 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 280 5 6 15 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 280 (accept_3_3 29
  75 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 280
  (Polychromatic418967fa.accept_16_12_11_8_1_832 28 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 280 (Polychromatic418967fa.accept_21_6_12_7_1_11386 27 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 280 (accept_3_3 26 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 75 280 5 5 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 75 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 280 (accept_3_3 23 75 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 75 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 280
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 75 280 5 4 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 75 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 280 (accept_3_3 17 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16
  75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 280 5 3 15 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 280 (accept_3_3 14
  75 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 280 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 280 (accept_3_3 11 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 75 280 5 2 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 75 280 (Polychromatic418967fa.accept_24_9_3_16_1_17175 9 75 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 280 (accept_3_3 8 75 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 75 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 75 280 5 1 15 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 75 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 280 (accept_3_3 2 75 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 280 (allA_of_3_1 74 74
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 280 (allA_succ_of_accept 72 73 280
  (Polychromatic418967fa.accept_15_12_13_10_1_812 72 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 280 (accept_3_3 71 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 280 (accept_3_3 68 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 280 (Polychromatic418967fa.accept_13_2_8_7_1_2424 67 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 280
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 66 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 280 (accept_3_3 65 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 64 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 280 (accept_3_3 62 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 61 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 280
  (Polychromatic418967fa.accept_16_12_9_8_1_2508 60 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 280 (accept_3_3 59 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 280 (accept_3_3 56 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 55 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 280
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 280 (accept_3_3 53 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 280 (Polychromatic418967fa.accept_16_4_9_8_1_2509 52 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 280 (accept_3_3 50 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 280
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 48 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 280 (accept_3_3 47 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 280 (accept_3_3 44 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 280 (Polychromatic418967fa.accept_19_5_16_14_1_2374 43 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 42 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 280 (accept_3_3 41 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 40 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 280 (accept_3_3 38 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 280 (Polychromatic418967fa.accept_17_3_5_8_1_1687 37 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 280
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 280 (accept_3_3 35 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 280 (accept_3_3 32 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 280
  (Polychromatic418967fa.accept_17_13_5_8_1_896 30 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 280 (accept_3_3 29 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 280 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 280 (accept_3_3 26 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 280 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 280
  (Polychromatic418967fa.accept_19_5_16_14_1_2374 24 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 280 (accept_3_3 23 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 280 (accept_3_3 20 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 280
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 280 (accept_3_3 17 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 280 (accept_3_3 14 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 280 (Polychromatic418967fa.accept_17_13_5_8_1_896 13 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 280
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 280 (accept_3_3 11 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 280 (accept_3_3 8 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 280 (Polychromatic418967fa.accept_16_7_9_8_1_829 7 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 280
  (Polychromatic418967fa.accept_24_6_1_16_1_12200 6 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 280 (accept_3_3 5 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 73 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 280 (accept_3_3 2 73 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 73 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 280 (allA_succ_of_accept 71
  72 280 (accept_3_3 71 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 280 2 35 36 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 69 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 280 4 17 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 67 72 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 280 2 33 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 280 (accept_3_3 65 72 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 280 8 8 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 72 280 (Polychromatic418967fa.accept_17_12_4_8_1_5073 63 72 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 280 2 31 36 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 280
  (Polychromatic418967fa.accept_19_4_15_14_1_10614 61 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 72 280 4 15 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 72 280 (accept_3_3 59 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 72 280 2 29 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 72 280 (Polychromatic418967fa.accept_21_15_9_7_1_3780 57 72 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 280 8 7 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 280
  (Polychromatic418967fa.accept_19_17_15_14_1_3623 55 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 72 280 2 27 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 72 280 (accept_3_3 53 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 280 4 13 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 280 (Polychromatic418967fa.accept_15_6_12_10_1_1543 51 72 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 280 2 25 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 280
  (Polychromatic418967fa.accept_19_11_15_14_1_5018 49 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 72 280 8 6 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 72 280 (accept_3_3 47 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 280 2 23 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 72 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 72 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 280 4 11 18 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 280 2 21 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 72 280 (accept_3_3 41 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 280 8 5 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 72 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 72 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 280 2 19 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335
  37 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 280 4 9 18 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 280 (accept_3_3 35
  72 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 280 2 17 36 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 280
  (Polychromatic418967fa.accept_22_11_6_16_1_17174 33 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 72 280 8 4 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 72 280 (Polychromatic418967fa.accept_21_10_9_7_1_9857 31 72 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 280 2 15 36 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 280 (accept_3_3 29 72 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 280 4 7 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 280 (Polychromatic418967fa.accept_21_6_9_7_1_3752 27 72 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 280 2 13 36 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 280
  (Polychromatic418967fa.accept_27_25_18_10_1_15442 25 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 72 280 8 3 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 72 280 (accept_3_3 23 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 72 280 2 11 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 72 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 72 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 280 4 5 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 280 (Polychromatic418967fa.accept_21_19_9_7_1_8366
  19 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 280 2 9 36 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 280 (accept_3_3 17
  72 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 280 8 2 9 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 280
  (Polychromatic418967fa.accept_21_15_9_7_1_3780 15 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 72 280 2 7 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 280 (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 72 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 280 4 3 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 280 (accept_3_3 11 72 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 72 280 2 5 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 72 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 72 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 280 8 1 9 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 280
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 280 2 3 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 280 (accept_3_3 5 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 280
  4 1 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72
  280 (Polychromatic418967fa.accept_21_3_9_7_1_8369 3 72 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 72 280 2 1 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 72 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 72 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 280 (allA_of_3_1 71 71 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 280 (allA_succ_of_accept 69 70 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 69 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 280 2 34 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 70 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 70 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 280 2 33 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 70 280 5 13 14 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 70 280 2 32 35 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 70 280 7 9 10 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 70 280 2 31 35 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 280 10 6 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 70 280 (accept_3_3 59 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70
  280 2 29 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  57 70 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 70 280 14 4 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 70 280 5 11 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 70 280 2 27 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 70 280 (accept_3_3 53 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 280 2 26 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 70 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 70 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 280 10 5 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 70 280 7 7 10 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 70 280 2 24 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 280 (accept_3_3 47 70 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 280 2 23 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 70 280 5 9 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 70 280 2 22 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 43 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 280 14 3 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 70 280 (accept_3_3 41 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  280 10 4 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 70 280 2 19 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 70 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 70 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 280 2 18 35 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 280 35 1 2 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 70 280 2 17 35 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 280 2 16 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 70 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 70 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 280 10 3 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 280 (accept_3_3 29 70 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 280 14 2 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 70 280 (Polychromatic418967fa.accept_17_10_2_8_1_6295 27 70 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 280 2 13 35 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 70 280 5 5 14 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 70 280 2 12 35 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 280 (accept_3_3 23
  70 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 280 2 11 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 70 280 7 3 10 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 70 280 10 2 7 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 280 2 9 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 280 (accept_3_3 17 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  280 2 8 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 70
  280 5 3 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 70
  280 14 1 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13
  70 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 70 280 2 6 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 70 280 (accept_3_3 11 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 70 280 10 1 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 70 280 (Polychromatic418967fa.accept_22_9_4_16_1_4545 9 70 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 280 2 4 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 70 280 7 1 10 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 70 280 2 3 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 70 280 5 1 14 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 70 280 2 2 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 70 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 280 2 1 35 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 70 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 280
  (allA_succ_of_accept 68 69 280 (accept_3_3 68 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 280 (accept_3_3 65 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 64 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 280 (accept_3_3 62 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 280 (Polychromatic418967fa.accept_16_12_5_8_1_2492 60 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 280 (accept_3_3 59 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 69 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 280 (accept_3_3 56 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 280 (accept_3_3 53 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 280
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 51 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 280 (accept_3_3 50 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 280 (accept_3_3 47 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 46 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 280
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 280 (accept_3_3 44 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 280 (accept_3_3 41 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 280 (accept_3_3 38 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 280 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 280 (accept_3_3 35 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 69 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 280
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 280 (accept_3_3 32 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 280 (accept_3_3 29 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 280 (Polychromatic418967fa.accept_16_12_5_8_1_2492 28 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 280 (accept_3_3 26 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 280 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 280 (accept_3_3 23 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 69 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 280 (accept_3_3 20 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 280 (accept_3_3 17 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 69 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 280
  (Polychromatic418967fa.accept_24_15_21_16_1_12209 15 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 280 (accept_3_3 14 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 69 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 280 (accept_3_3 11 69 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 280 (Polychromatic418967fa.accept_13_10_4_7_1_2465
  10 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 280
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 280 (accept_3_3 8 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 280 (accept_3_3 5 69 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 69 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 69
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 280 (accept_3_3 2 69 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 280 (allA_of_3_1 68 68 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 280 (allA_succ_of_accept 66 67 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 280 (accept_3_3 65 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 64 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 280 (accept_3_3 62 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 280 (accept_3_3 59 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 280 (accept_3_3 56 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 280 (Polychromatic418967fa.accept_18_1_13_10_1_2024 55 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 280
  (Polychromatic418967fa.accept_21_12_4_7_1_8364 54 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 280 (accept_3_3 53 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 280 (accept_3_3 50 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 49 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 280 (accept_3_3 47 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 280 (accept_3_3 44 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 280 (accept_3_3 41 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 280 (Polychromatic418967fa.accept_18_4_13_10_1_2064 40 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 280 (accept_3_3 38 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 280 (Polychromatic418967fa.accept_16_5_3_8_1_4555 37 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 280
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 280 (accept_3_3 35 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 280 (accept_3_3 32 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 280 (Polychromatic418967fa.accept_13_5_2_7_1_2414 31 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 280 (accept_3_3 29 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 280 (accept_3_3 26 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 280 (accept_3_3 23 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 280 (accept_3_3 20 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 280
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 280 (accept_3_3 17 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 280 (accept_3_3 14 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 280 (Polychromatic418967fa.accept_16_13_3_8_1_2422 13 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 280 (accept_3_3 11 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 280 (accept_3_3 8 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 280 (accept_3_3 5 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  280 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 67 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 280 (accept_3_3 2 67 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 67 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 280 (allA_succ_of_accept 65 66
  280 (accept_3_3 65 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 280 2 32 33 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 280 2 31 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 66 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 66 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 280 2 30 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 280 (accept_3_3 59 66 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 280 2 29 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 57
  66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 280 2 28 33 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 280
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 55 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 280 2 27 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 66 280 (accept_3_3 53 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 66 280 2 26 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 66 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 66 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 280 2 25 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 280 2 24 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 66 280 (accept_3_3 47 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 280 2 23 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 66 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 66 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 280 2 22 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 280 2 21 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 66 280 (accept_3_3 41 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 280 2 20 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 66 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 66 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 280 2 19 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 280
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 280 2 18 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 66 280 (accept_3_3 35 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 280 2 17 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 66 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 66 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 280 2 16 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 280 2 15 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 66 280 (accept_3_3 29 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 280 2 14 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 66 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 66 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 280 2 13 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 280 2 12 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 66 280 (accept_3_3 23 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 280 2 11 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 66 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 280 2 10 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 280
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 280 2 9 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 280 (accept_3_3 17 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  280 2 8 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 280 2 7 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 66 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 66 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 280 2 6 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 280 (accept_3_3 11 66 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 280 2 5 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 280 2 4 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 280 2 3 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 280 (accept_3_3 5 66 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 280 2 2 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 280 2 1 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 1
  66 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 280 (allA_of_3_1 65 65 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 280 (allA_succ_of_accept 63 64 280
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 63 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 280 2 31 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 64 280 (Polychromatic418967fa.accept_19_4_7_14_1_3537 61 64 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 280 4 15 16 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 280 (accept_3_3 59 64 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 280 2 29 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080
  57 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 280 8 7 8 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 280
  (Polychromatic418967fa.accept_17_4_13_8_1_3874 55 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 280 2 27 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 64 280 (accept_3_3 53 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 64 280 4 13 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 64 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 51 64 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 280 2 25 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079
  49 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 64 280 8 6 8 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 280 (accept_3_3 47
  64 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 280 2 23 32 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 280
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 64 280 4 11 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 64 280 (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 64 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 280 2 21 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 280 (accept_3_3 41 64 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 280 8 5 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 64 280 (Polychromatic418967fa.accept_15_9_4_10_1_2316 39 64 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 280 2 19 32 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 280
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 280 4 9 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 280 (accept_3_3 35 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  280 2 17 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 64 280 (Polychromatic418967fa.accept_21_12_1_7_1_17173 33 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 280 8 4 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 64 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 64 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 280 2 15 32 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 280 (accept_3_3 29 64 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 280 4 7 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 280 (Polychromatic418967fa.accept_19_8_7_14_1_13279 27 64
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 280 2 13 32 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 280
  (Polychromatic418967fa.accept_19_6_7_14_1_1343 25 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 280 8 3 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 280 (accept_3_3 23 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  280 2 11 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 64 280 (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 280 4 5 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 64 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 280 2 9 32 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 280 (accept_3_3 17 64 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 280 8 2 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 64 280 (Polychromatic418967fa.accept_17_15_13_8_1_7603 15 64
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 280 2 7 32 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 280
  (Polychromatic418967fa.accept_15_13_4_10_1_821 13 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 280 4 3 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 280 (accept_3_3 11 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  280 2 5 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 280 (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 280 8 1 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 64 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 280 2 3 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 280 (accept_3_3 5 64 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 280 4 1 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 280 (Polychromatic418967fa.accept_17_3_13_8_1_11337 3 64 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 280 2 1 32 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 280
  (Polychromatic418967fa.accept_30_1_4_10_1_17172 1 64 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 280
  (allA_succ_of_accept 62 63 280 (accept_3_3 62 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 280 (Polychromatic418967fa.accept_16_12_15_8_1_4586 60 63 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 280 (accept_3_3 59 63 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 63 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 280
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 63 280 7 8 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 63 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 63 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 280 (accept_3_3 53 63 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 280 (Polychromatic418967fa.accept_15_7_3_10_1_817
  52 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 280
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 280 (accept_3_3 50 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63
  280 7 7 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  63 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 280 (accept_3_3 47 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 280 (Polychromatic418967fa.accept_19_7_6_14_1_11872 45 63
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 280 (accept_3_3 44 63 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 280 7 6 9 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 280 (accept_3_3 41
  63 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 280
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 63 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 280 (accept_3_3 38 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 63 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 280 (Polychromatic418967fa.accept_11_3_8_5_1_336
  36 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 63 280 7 5 9 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 280
  (Polychromatic418967fa.accept_22_12_19_16_1_9551 34 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 63 280 (Polychromatic418967fa.accept_16_1_15_8_1_2411 33 63 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 280 (accept_3_3 32 63 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 280 (accept_3_3 29 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63
  280 7 4 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  63 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 63 280 (accept_3_3 26 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 63 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 280 (accept_3_3 23 63 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077
  22 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 280 7 3 9 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 280 (accept_3_3 20
  63 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 280 (accept_3_3 17 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 63 280 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 63 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 280
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 63 280 7 2 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 63 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 280 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 63
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 280 (accept_3_3 11 63 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 280
  (Polychromatic418967fa.accept_17_10_12_8_1_2748 10 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 63 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 280 (accept_3_3 8 63 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 63 280 7 1 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 63 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 63 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 280 (accept_3_3 5 63 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 280 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 63 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 3 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 280 (accept_3_3 2 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 280 (allA_of_3_1 62 62
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 280 (allA_succ_of_accept 60 61 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 280 (accept_3_3 59 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 280 (accept_3_3 56 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 55 61 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 280 (accept_3_3 53 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 280 (accept_3_3 50 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 280 (accept_3_3 47 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 280 (accept_3_3 44 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 61 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 280 (accept_3_3 41 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 280 (accept_3_3 38 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 280 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 61 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 280
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 280 (accept_3_3 35 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 280 (accept_3_3 32 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 61 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 280 (accept_3_3 29 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 28 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 280 (accept_3_3 26 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 280 (Polychromatic418967fa.accept_21_4_19_7_1_5142 25 61 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 280 (accept_3_3 23 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 280 (accept_3_3 20 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 61 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 280
  (Polychromatic418967fa.accept_19_18_4_14_1_14577 18 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 61 280 (accept_3_3 17 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 61 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 61 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 280 (accept_3_3 14 61 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 280 (accept_3_3 11 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 280 (accept_3_3 8 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 61 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 280 (accept_3_3 5 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 61 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 280 (accept_3_3 2 61 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 61 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 280 (allA_succ_of_accept 59 60 280 (accept_3_3 59 60 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 280 2 29 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 60 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 60 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 280 4 14 15 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 60 280 5 11 12 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 280 2 27 30 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 280 (accept_3_3 53 60 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 280 4 13 15 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 280
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 60 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 280 10 5 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 280 4 12 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 280 (accept_3_3 47 60 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 280 2 23 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 280 5 9 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 280 4 11 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 60 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 280 2 21 30 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 280 (accept_3_3 41
  60 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 280 20 2 3 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 280 2 19 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 60 280 (Polychromatic418967fa.accept_16_5_12_8_1_2521 37 60 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 280 4 9 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 280 5 7 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 280 2 17 30 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 280
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 33 60 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 280 4 8 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 60 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 280 10 3 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 280 (accept_3_3 29 60 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 280 4 7 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 60 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 280 2 13 30 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 280 5 5 12 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 280 4 6 15 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 280 (accept_3_3 23 60 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 280 2 11 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  60 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 280 20 1 3 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 280
  (Polychromatic418967fa.accept_16_3_12_8_1_808 19 60 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 280 2 9 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 280 (accept_3_3 17 60 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  280 4 4 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60
  280 5 3 12 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60
  280 2 7 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13
  60 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 60 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 60 280 4 3 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 60 280 (accept_3_3 11 60 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 60 280 10 1 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 60 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 60 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 280 4 2 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 280 2 3 30 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 280 5 1 12 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 280 4 1 15 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 280 2 1 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 60 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 280 (allA_of_3_1 59 59 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 280
  (allA_succ_of_accept 57 58 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 58 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 280 2 28 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 280 (Polychromatic418967fa.accept_12_7_10_4_1_382
  55 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 280 2 27 29 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 280
  (accept_3_3 53 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 280 2 26 29 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 58 280 2 25 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 58 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 58 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 280 2 24 29 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 280 (accept_3_3 47 58 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 280 2 23 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 280 (Polychromatic418967fa.accept_21_3_16_7_1_12858
  45 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 280 2 22 29 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 280 2 21 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 58 280 (accept_3_3 41 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 58 280 2 20 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 58 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 58 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 58 280 2 19 29 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 58 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 58 280 2 18 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 58 280 (accept_3_3 35 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 58 280 2 17 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 58 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 58 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 280 2 16 29 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 280 2 15 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 58 280 (accept_3_3 29 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 58 280 2 14 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 58 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 58 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 280 2 13 29 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 280 2 12 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 58 280 (accept_3_3 23 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 58 280 2 11 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 58 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 58 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 58 280 2 10 29 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 58 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 58 280 2 9 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 58 280 (accept_3_3 17 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58
  280 2 8 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  58 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 58 280 2 7 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 58 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 58 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 280 2 6 29 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 280 (accept_3_3 11 58 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 280 2 5 29 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 280
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 280 2 4 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 280 2 3 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 280 (accept_3_3 5 58 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 280 2 2 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 58 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 280 2 1 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  58 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 280 (allA_succ_of_accept 56 57 280
  (accept_3_3 56 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 57 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 280 (accept_3_3 53 57 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 57 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 280 (accept_3_3 50 57
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 280
  (Polychromatic418967fa.accept_17_14_6_8_1_7688 48 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 280 (accept_3_3 47 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 280 (Polychromatic418967fa.accept_22_2_13_16_1_6117 46 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 280 (Polychromatic418967fa.accept_21_3_15_7_1_5155 45 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 280 (accept_3_3 44 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 280 (accept_3_3 41 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 280 (accept_3_3 38 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 280
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 280 (accept_3_3 35 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 57 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 280 (accept_3_3 32 57 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 280
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 280 (accept_3_3 29 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 280 (Polychromatic418967fa.accept_24_3_9_16_1_8812 27 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 280 (accept_3_3 26 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 280 (accept_3_3 23 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 280 (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 280 (accept_3_3 20 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 280 (accept_3_3 17 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 57 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 280 (accept_3_3 14 57 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 280
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 280 (accept_3_3 11 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 280 (Polychromatic418967fa.accept_21_10_15_7_1_3784 10 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 57 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 280 (accept_3_3 8 57 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 280 (accept_3_3 5 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 57 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 280 (Polychromatic418967fa.accept_21_3_15_7_1_5155 3 57 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 280 (accept_3_3 2 57 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 280 (allA_of_3_1 56 56 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 280
  (allA_succ_of_accept 54 55 280 (Polychromatic418967fa.accept_19_16_17_14_1_4969 54 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 280 (accept_3_3 53 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 280 (Polychromatic418967fa.accept_16_4_7_8_1_5753 52 55 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 280 5 10 11 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 280
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 48 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 280 (accept_3_3 47 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 55 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 280 5 9 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 280 (accept_3_3 44 55 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 55 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 280
  (Polychromatic418967fa.accept_22_20_11_16_1_6236 42 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 55 280 (accept_3_3 41 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 55 280 5 8 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 55 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 280 (accept_3_3 38 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 55 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 55 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 280
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 55 280 5 7 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 55 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 280 (accept_3_3 32 55 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 280 (Polychromatic418967fa.accept_16_15_7_8_1_8189
  31 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 280 5 6 11 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 280 (accept_3_3 29
  55 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 280
  (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 55 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 280 (accept_3_3 26 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 55 280 5 5 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 55 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 55 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 280 (accept_3_3 23 55 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 55 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 55 280 5 4 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 55 280 (Polychromatic418967fa.accept_21_19_13_7_1_3706 19 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 280 (Polychromatic418967fa.accept_17_1_4_8_1_5049 18 55 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 280 (accept_3_3 17 55 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 280
  (Polychromatic418967fa.accept_18_16_1_10_1_2029 16 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 55 280 5 3 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 55 280 (accept_3_3 14 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 280 (Polychromatic418967fa.accept_17_13_4_8_1_3830 13 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 280 (Polychromatic418967fa.accept_16_12_7_8_1_1589 12 55 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 280 (accept_3_3 11 55 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55 280 5 2 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 55 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 280 (accept_3_3 8 55 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 280 (Polychromatic418967fa.accept_17_7_4_8_1_7678 7
  55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 280
  (Polychromatic418967fa.accept_21_6_13_7_1_8394 6 55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 55 280 5 1 11 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 55 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 55 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 280 (accept_3_3 2 55 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1
  55 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 280 (allA_succ_of_accept 53 54 280
  (accept_3_3 53 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 280 2 26 27 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 280 2 25 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 54 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 49 54 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 280 2 24 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 280 (accept_3_3 47 54 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 280 2 23 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45
  54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 280 2 22 27 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 280
  (Polychromatic418967fa.accept_19_5_16_14_1_2374 43 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 280 2 21 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 54 280 (accept_3_3 41 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 54 280 2 20 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 54 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 54 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 280 2 19 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 280 2 18 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 54 280 (accept_3_3 35 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 280 2 17 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 54 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 280 2 16 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 280
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 31 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 280 2 15 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 54 280 (accept_3_3 29 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 280 2 14 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 54 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 54 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 280 2 13 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 280
  (Polychromatic418967fa.accept_21_4_12_7_1_5174 25 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 280 2 12 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 54 280 (accept_3_3 23 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 54 280 2 11 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 54 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 280 2 10 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 280
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 19 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 280 2 9 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 280 (accept_3_3 17 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  280 2 8 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 280 2 7 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 54 280 (Polychromatic418967fa.accept_17_13_3_8_1_6310 13 54 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 280 2 6 27 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 280 (accept_3_3 11 54 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 280 2 5 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 280 2 4 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 280 (Polychromatic418967fa.accept_22_7_10_16_1_17171 7 54 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 280 2 3 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 280 (accept_3_3 5 54 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 280 2 2 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 54 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 280 2 1 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 1
  54 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 280 (allA_of_3_1 53 53 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 280 (allA_succ_of_accept 51 52 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51
  52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 280 2 25 26 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 52 280 4 12 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 52 280 (accept_3_3 47 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52
  280 2 23 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  45 52 280 (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 52 280 4 11 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 52 280 (Polychromatic418967fa.accept_16_11_4_8_1_3435 43 52 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 280 2 21 26 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 280 (accept_3_3 41 52 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 280 4 10 13 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 52 280 2 19 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 52 280 (Polychromatic418967fa.accept_16_5_4_8_1_1560 37 52 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 280 4 9 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 280 (accept_3_3 35 52 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 280 2 17 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 52 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 280 4 8 13 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 280 2 15 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 52 280 (accept_3_3 29 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 52 280 4 7 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 52 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 52 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 280 2 13 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 25
  52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 280 4 6 13 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 280 (accept_3_3 23
  52 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 280 2 11 26 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 52 280 4 5 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 52 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 52 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 280 2 9 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 280 (accept_3_3 17 52 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 280 4 4 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 52 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 52 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 280 2 7 26 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 280 4 3 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 280 (accept_3_3 11 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  280 2 5 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 280 (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 280 4 2 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 280 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7 52 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 280 2 3 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 280 (accept_3_3 5 52 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 280 4 1 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 52 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 280 2 1 26 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 280
  (Polychromatic418967fa.accept_15_1_7_10_1_287 1 52 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 280)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 280 (allA_succ_of_accept 50 51 280
  (accept_3_3 50 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 51 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 280 (accept_3_3 47 51 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 51 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131
  45 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 280 (accept_3_3 44
  51 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 51 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 280 (accept_3_3 41 51 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 51 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39
  51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 280 (accept_3_3 38 51
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  37 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 280
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 280 (accept_3_3 35 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 51 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 280 (accept_3_3 32 51 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 280 (accept_3_3 29 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 280 (Polychromatic418967fa.accept_16_12_3_8_1_5729 28 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 51 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 280 (accept_3_3 26 51 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 280
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 280 (accept_3_3 23 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 280 (accept_3_3 20 51 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 280 (accept_3_3 17 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 280 (Polychromatic418967fa.accept_19_15_13_14_1_5015 15 51 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 280 (accept_3_3 14 51 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 280 (accept_3_3 11 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 51 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 280 (accept_3_3 8 51 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 280 (accept_3_3 5 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 51 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 51 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 280 (accept_3_3 2 51 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 280)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 280 (allA_of_3_1 50 50 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 280
  (allA_succ_of_accept 48 49 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 280 (accept_3_3 47 49 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 49 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 280 (accept_3_3 44 49
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 49 280 7 6 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 49 280 (accept_3_3 41 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 280 (Polychromatic418967fa.accept_17_6_15_8_1_1714 40 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 280 (accept_3_3 38 49 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 49 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 280
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 49 280 7 5 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 49 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 280 (accept_3_3 32 49 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 280 (Polychromatic418967fa.accept_16_15_1_8_1_1585
  31 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 280 (accept_3_3 29 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49
  280 7 4 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  49 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 49 280 (accept_3_3 26 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 49 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 280 (accept_3_3 23 49 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 280 (Polychromatic418967fa.accept_12_10_1_4_1_392
  22 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 49 280 7 3 7 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 49 280 (accept_3_3 20
  49 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 280
  (Polychromatic418967fa.accept_18_1_13_10_1_2024 19 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 280 (Polychromatic418967fa.accept_22_18_5_16_1_11118 18 49 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 280 (accept_3_3 17 49 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15
  49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 49 280 7 2 7 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 49 280
  (Polychromatic418967fa.accept_15_13_4_10_1_821 13 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 49 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 280 (accept_3_3 11 49 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 49 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 49 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 280 (accept_3_3 8 49 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 280 7 1 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 280 (accept_3_3 5 49 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 280 (Polychromatic418967fa.accept_13_4_10_7_1_1701
  4 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 280 (accept_3_3 2 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  280 (Polychromatic418967fa.accept_18_1_13_10_1_2024 1 49 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 280))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 280 (allA_succ_of_accept
  47 48 280 (accept_3_3 47 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 280 2 23 24 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 280
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 280 4 11 12 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 48 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 280 2 21 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 280 (accept_3_3 41 48 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 280 8 5 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 48 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 280 2 19 24 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 280
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 280 4 9 12 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 280 (accept_3_3 35 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  280 2 17 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  33 48 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 280 8 4 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 280 2 15 24 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 280 (accept_3_3 29 48 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 280 4 7 12 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 280 (Polychromatic418967fa.accept_18_9_12_10_1_387 27 48 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 280 2 13 24 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 280 8 3 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 280 (accept_3_3 23 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48
  280 2 11 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 48 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 48 280 4 5 12 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 48 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 280 2 9 24 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 280 (accept_3_3 17 48 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 280 8 2 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 48 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 280 2 7 24 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 280 4 3 12 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 280 (accept_3_3 11 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48
  280 2 5 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  48 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 48 280 8 1 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 48 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 280 2 3 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 280 (accept_3_3 5 48 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 280 4 1 12 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 48 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 48 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 280 2 1 24 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 280
  (Polychromatic418967fa.accept_19_1_10_14_1_3597 1 48 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 280)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 280 (allA_of_3_1 47 47 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 280 (allA_succ_of_accept 45 46 280
  (Polychromatic418967fa.accept_19_7_8_14_1_13273 45 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 280 2 22 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 46 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 46 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 280 2 21 23 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 280 (accept_3_3 41 46 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 280 2 20 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316
  39 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 280 2 19 23 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 280 2 18 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 46 280 (accept_3_3 35 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 46 280 2 17 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 46 280 (Polychromatic418967fa.accept_21_12_4_7_1_8364 33 46 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 280 2 16 23 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 280 2 15 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 46 280 (accept_3_3 29 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 46 280 2 14 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 46 280 (Polychromatic418967fa.accept_17_10_12_8_1_2748 27 46 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 280 2 13 23 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 280 2 12 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 46 280 (accept_3_3 23 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 46 280 2 11 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 46 280 (Polychromatic418967fa.accept_15_6_1_10_1_1549 21 46 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 280 2 10 23 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 280
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 280 2 9 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 280 (accept_3_3 17 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  280 2 8 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 280 (Polychromatic418967fa.accept_25_15_21_5_1_17170 15 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 280 2 7 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 46 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 46 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 280 2 6 23 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 280 (accept_3_3 11 46 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 280 2 5 23 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 280
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 46 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 280 2 4 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 46 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 280 2 3 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 280 (accept_3_3 5 46 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 280 2 2 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 280 (Polychromatic418967fa.accept_17_3_12_8_1_1688 3 46 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 280 2 1 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  46 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  280)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 280 (allA_succ_of_accept 44 45 280 (accept_3_3 44 45
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 280 (accept_3_3 41 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45
  280 5 8 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  45 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 280 (accept_3_3 38 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 280 (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 45
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 280 5 7 9 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 280
  (Polychromatic418967fa.accept_19_15_7_14_1_11879 34 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 280 (Polychromatic418967fa.accept_18_15_9_10_1_1082 33 45 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 280 (accept_3_3 32 45 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 280 5 6 9 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 280 (accept_3_3 29 45 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388
  28 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 280
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 280 (accept_3_3 26 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45
  280 5 5 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  45 280 (Polychromatic418967fa.accept_27_24_18_10_1_17169 24 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 280 (accept_3_3 23 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 280 (Polychromatic418967fa.accept_13_9_6_7_1_551 22 45 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 280 (Polychromatic418967fa.accept_16_5_13_8_1_2454 21 45
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 45 280 5 4 9 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 45 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 280 (accept_3_3 17 45 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 45 280 (Polychromatic418967fa.accept_21_16_3_7_1_6705 16 45 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 280 5 3 9 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 280 (accept_3_3 14 45 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 280
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 280 (accept_3_3 11 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45
  280 5 2 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45
  280 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 280 (accept_3_3 8 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 45 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 45 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 280 5 1 9 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 280 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 45 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 280
  (Polychromatic418967fa.accept_16_3_13_8_1_1594 3 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 280 (accept_3_3 2 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 280))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 280 (allA_of_3_1 44 44 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 43 280 (allA_succ_of_accept 42 43 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 280 (accept_3_3 41 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 280 (accept_3_3 38 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 43 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 280
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 280 (accept_3_3 35 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 280 (accept_3_3 32 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 43 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 280 (accept_3_3 29 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 280 (accept_3_3 26 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 43 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 280 (accept_3_3 23 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 280 (accept_3_3 20 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 280 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 43 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 280
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 280 (accept_3_3 17 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 280 (accept_3_3 14 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 43 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 280 (accept_3_3 11 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 280 (accept_3_3 8 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 280 (Polychromatic418967fa.accept_23_7_20_4_1_12517 7 43 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 280 (accept_3_3 5 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 280 (accept_3_3 2 43 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 43 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 280))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 280
  (allA_succ_of_accept 41 42 280 (accept_3_3 41 42 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42
  280 2 20 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 42 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 42 280 2 19 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 42 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 42 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 280 2 18 21 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 280 7 5 6 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 42 280 2 17 21 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 280 2 16 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 42 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 280 2 15 21 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 280 (accept_3_3 29 42 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 280 14 2 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 280 2 13 21 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 280 2 12 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 42 280 (accept_3_3 23 42 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 280 2 11 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 42 280 7 3 6 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 42 280 2 10 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 280 (Polychromatic418967fa.accept_24_19_18_16_1_5216 19 42 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 280 2 9 21 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 280 (accept_3_3 17 42 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 280 2 8 21 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 15 42 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 42 280 14 1 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 42 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 280 2 6 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 280 (accept_3_3 11 42 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 280 2 5 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 280 2 4 21 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 42 280 7 1 6 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 280 2 3 21 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 280 (accept_3_3 5 42 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 280 2 2 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 280 2 1 21 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 280
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 42 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 280)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 280 (allA_of_3_1 41 41 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 40 280 (allA_succ_of_accept 39 40 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 40 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 280 2 19 20 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 40 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 40 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 280 4 9 10 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 40 280 5 7 8 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 40 280 2 17 20 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 40 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 40 280 8 4 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 40 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 40 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 280 10 3 4 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 280 (accept_3_3 29 40 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 40 280 4 7 10 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 40 280 (Polychromatic418967fa.accept_19_8_2_14_1_3640 27 40 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 280 2 13 20 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 40 280 5 5 8 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 40 280 8 3 5 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 280 (accept_3_3 23 40 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 280 2 11 20 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  40 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 280 20 1 2 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 280
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 40 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 280 2 9 20 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 280 (accept_3_3 17 40 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40
  280 8 2 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 40
  280 5 3 8 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 40
  280 2 7 20 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13
  40 280 (Polychromatic418967fa.accept_18_13_4_10_1_1076 13 40 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 40 280 4 3 10 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 40 280 (accept_3_3 11 40 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 40 280 10 1 4 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 40 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 40 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 280 8 1 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 280 2 3 20 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 40 280 5 1 8 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 40 280 4 1 10 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 40 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 40 280 2 1 20 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 40 280 (Polychromatic418967fa.accept_19_1_2_14_1_3666 1 40 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 40 280)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 280
  (allA_succ_of_accept 38 39 280 (accept_3_3 38 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  39 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 39 280 (Polychromatic418967fa.accept_16_4_7_8_1_5753 36 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 280 (accept_3_3 35 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 39 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 280 (accept_3_3 32 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 280 (accept_3_3 29 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 280 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 39 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 280 (accept_3_3 26 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 280 (accept_3_3 23 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 39 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 280 (accept_3_3 20 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 280 (accept_3_3 17 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 39 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 280 (accept_3_3 14 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 280 (accept_3_3 11 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 39 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 280
  (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 280 (accept_3_3 8 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 39 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 280 (accept_3_3 5 39 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 39 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 280 (Polychromatic418967fa.accept_15_3_9_10_1_2325
  3 39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 280 (accept_3_3 2 39
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  39 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  280))))))))))))))))))))))))))))))))))))))) (allB_succ 38 280 (allA_of_3_1 38 38 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 280 (allA_succ_of_accept 36 37 280 (Polychromatic418967fa.accept_16_4_5_8_1_2425 36 37 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 280 (accept_3_3 35 37 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 280 (Polychromatic418967fa.accept_12_10_1_4_1_392
  34 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 280 (accept_3_3 32 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 280 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 280 (Polychromatic418967fa.accept_13_4_11_7_1_558 30 37 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 280 (accept_3_3 29 37 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 280 (Polychromatic418967fa.accept_16_12_5_8_1_2492 28 37 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 280 (accept_3_3 26 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 280 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 280 (Polychromatic418967fa.accept_21_3_16_7_1_12858 24 37 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 280 (accept_3_3 23 37 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 37 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 280 (accept_3_3 20 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 280 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 37 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 280 (accept_3_3 17 37 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 280 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 37 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 280 (accept_3_3 14 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 280 (Polychromatic418967fa.accept_16_13_5_8_1_5814 13 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 280 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 37 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 280 (accept_3_3 11 37 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 37 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 280 (accept_3_3 8 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  280 (Polychromatic418967fa.accept_19_7_18_14_1_9185 7 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 280 (Polychromatic418967fa.accept_21_6_16_7_1_3714 6 37 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 280 (accept_3_3 5 37 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 280 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 37 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 280 (accept_3_3 2 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 37 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 37 280))))))))))))))))))))))))))))))))))))) (allB_succ 36 280 (allA_succ_of_accept 35 36 280
  (accept_3_3 35 36 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 280 2 17 18 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 280
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 36 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 280 4 8 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 31 36 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 280 2 15 18 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 280 (accept_3_3 29 36 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 280 4 7 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 36 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 36 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 280 2 13 18 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 280
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 36 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 280 4 6 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 280 (accept_3_3 23 36 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36
  280 2 11 18 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 36 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 36 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 36 280 4 5 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 36 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 280 2 9 18 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 280 (accept_3_3 17 36 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 280 4 4 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 280 (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 36 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 280 2 7 18 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 280
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 13 36 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 280 4 3 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 280 (accept_3_3 11 36 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36
  280 2 5 18 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  36 280 (Polychromatic418967fa.accept_16_9_4_8_1_2533 9 36 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 36 280 4 2 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 36 280 (Polychromatic418967fa.accept_16_7_4_8_1_2487 7 36 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 280 2 3 18 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 280 (accept_3_3 5 36 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 280 4 1 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 36 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 36 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 280 2 1 18 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 280
  (Polychromatic418967fa.accept_15_1_6_10_1_23 1 36 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 280)))))))))))))))))))))))))))))))))))) (allB_succ 35 280 (allA_of_3_1 35 35 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 280 (allA_succ_of_accept 33 34 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 33
  34 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 280 2 16 17 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 34 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 280 2 15 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 34 280 (accept_3_3 29 34 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 34 280 2 14 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 34 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 34 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 280 2 13 17 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 34 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 280 2 12 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 34 280 (accept_3_3 23 34 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 34 280 2 11 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 34 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 34 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 34 280 2 10 17 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 34 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 34 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 34 280 2 9 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 34 280 (accept_3_3 17 34 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34
  280 2 8 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  34 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 34 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 34 280 2 7 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 34 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 34 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 34 280 2 6 17 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 34 280 (accept_3_3 11 34 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34 280 2 5 17 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 34 280
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 34 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 34 280 2 4 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 34 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 34 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 280 2 3 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 280 (accept_3_3 5 34 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 34 280 2 2 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 34 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 34 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 280 2 1 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  34 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 280))))))))))))))))))))))))))))))))))
  (allB_succ 33 280 (allA_succ_of_accept 32 33 280 (accept_3_3 32 33 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 33 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 33 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 280 (accept_3_3 29 33 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 280
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 33 280 (Polychromatic418967fa.accept_18_9_15_10_1_395 27 33 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 280 (accept_3_3 26 33 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 33 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312
  24 33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 280 (accept_3_3 23
  33 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 22 33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 33 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 280 (accept_3_3 20 33 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 33 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18
  33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 280 (accept_3_3 17 33
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 16 33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 33 280 (Polychromatic418967fa.accept_16_15_1_8_1_1585 15 33 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 280 (accept_3_3 14 33 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 33 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 12
  33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 280 (accept_3_3 11 33
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 280
  (Polychromatic418967fa.accept_25_10_8_5_1_17168 10 33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 33 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 33 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 280 (accept_3_3 8 33 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 33 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 6
  33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 280 (accept_3_3 5 33 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4
  33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 280 (accept_3_3 2 33 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 280))))))))))))))))))))))))))))))))) (allB_succ 32 280 (allA_of_3_1 32 32 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 31 280 (allA_succ_of_accept 30 31 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 31
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 280 (accept_3_3 29 31 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695
  28 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 280 (accept_3_3 26 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 280 (accept_3_3 23 31 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 31 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 280 (accept_3_3 20 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 280 (Polychromatic418967fa.accept_18_1_13_10_1_2024 19 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 31 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 280 (accept_3_3 17 31 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 31 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 280 (accept_3_3 14 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 280 (accept_3_3 11 31 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 31 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 280 (accept_3_3 8 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 31 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 280 (accept_3_3 5 31 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 280 (Polychromatic418967fa.accept_16_4_15_8_1_2413 4 31 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 280 (accept_3_3 2 31 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 280 (Polychromatic418967fa.accept_16_1_15_8_1_2411
  1 31 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 280)))))))))))))))))))))))))))))))
  (allB_succ 30 280 (allA_succ_of_accept 29 30 280 (accept_3_3 29 30 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 280 2 14 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 30 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 30 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 280 2 13 15 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 280 5 5 6 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 280 2 12 15 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 280 (accept_3_3 23 30 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 280 2 11 15 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 280 10 2 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 280 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 30 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 280 2 9 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 280 (accept_3_3 17 30 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 280 2 8 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 280 5 3 6 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 280 2 7 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 30 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 280 2 6 15 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 280 (accept_3_3 11
  30 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 280 10 1 3 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 280 2 4 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 280 2 3 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 280 5 1 6 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 280 2 2 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 30 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 280 2 1 15 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 280
  (Polychromatic418967fa.accept_24_1_6_16_1_17167 1 30 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 280)))))))))))))))))))))))))))))) (allB_succ 29 280 (allA_of_3_1 29 29 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 28 280 (allA_succ_of_accept 27 28 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 28 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 280 2 13 14 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 280
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 25 28 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 28 280 4 6 7 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 28 280 (accept_3_3 23 28 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28
  280 2 11 14 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21
  28 280 7 3 4 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20
  28 280 4 5 7 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  19 28 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 28 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 28 280 2 9 14 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 28 280 (accept_3_3 17 28 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 28 280 4 4 7 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 28 280 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 28 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 280 14 1 2 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 280 (Polychromatic418967fa.accept_16_13_12_8_1_2451 13 28
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 280 4 3 7 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 280 (accept_3_3 11
  28 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 280 2 5 14 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 280
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 28 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 280 4 2 7 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 28 280 7 1 4 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 28 280 2 3 14 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 280 (accept_3_3 5 28 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 280
  4 1 7 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 280
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 3 28 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 280 2 1 14 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 28 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 280)))))))))))))))))))))))))))) (allB_succ 27 280 (allA_succ_of_accept 26
  27 280 (accept_3_3 26 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 27 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 280 (accept_3_3 23 27 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 27 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 280
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 280 (accept_3_3 20 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 27 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 280 (accept_3_3 17 27 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 27 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 280
  (Polychromatic418967fa.accept_17_15_10_8_1_1708 15 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 280 (accept_3_3 14 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 280 (Polychromatic418967fa.accept_16_12_11_8_1_832 12 27 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 280 (accept_3_3 11 27 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 280 (Polychromatic418967fa.accept_22_10_5_16_1_17166 10 27
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 280 (accept_3_3 8 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 280 (accept_3_3 5 27 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 280 (Polychromatic418967fa.accept_16_4_11_8_1_1574 4 27 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3
  27 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 280 (accept_3_3 2 27 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 280)))))))))))))))))))))))))))
  (allB_succ 26 280 (allA_of_3_1 26 26 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 280
  (allA_succ_of_accept 24 25 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 25 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 280 (accept_3_3 23 25 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 25 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 280 5 4 5 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 25 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 25 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 280 (accept_3_3 17 25 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 280 (Polychromatic418967fa.accept_21_16_4_7_1_5191 16 25 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 25 280 5 3 5 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 25 280 (accept_3_3 14 25 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 25 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 25 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 280 (accept_3_3 11 25 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25
  280 5 2 5 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25
  280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 280 (accept_3_3 8 25 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  280 (Polychromatic418967fa.accept_16_7_9_8_1_829 7 25 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 25 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 25 280 5 1 5 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 25 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 280 (accept_3_3 2 25 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  280 (Polychromatic418967fa.accept_16_1_9_8_1_2438 1 25 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 25 280))))))))))))))))))))))))) (allB_succ 24 280 (allA_succ_of_accept 23 24 280 (accept_3_3 23
  24 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 280 2 11 12 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 280 4 5 6 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 24 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 280 2 9 12 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 280 (accept_3_3 17 24 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 280 8 2 3 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 24 280 (Polychromatic418967fa.accept_18_15_6_10_1_5590 15 24 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 280 2 7 12 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 24 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 280 4 3 6 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 280 (accept_3_3 11 24 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  280 2 5 12 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 24 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 280 8 1 3 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 280 2 3 12 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 280 (accept_3_3 5 24 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 280 4 1 6 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 280 2 1 12 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 280
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 24 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 280)))))))))))))))))))))))) (allB_succ 23 280 (allA_of_3_1 23 23 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 280 (allA_succ_of_accept 21 22 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 22 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 280 2 10 11 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 22 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 280 2 9 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 280 (accept_3_3 17 22 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  280 2 8 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 22 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 280 2 7 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 22 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 22 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 280 2 6 11 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 280 (accept_3_3 11 22 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 280 2 5 11 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 280
  (Polychromatic418967fa.accept_19_9_3_14_1_2400 9 22 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 280 2 4 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 280 2 3 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 280 (accept_3_3 5 22 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 280 2 2 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 22 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 280 2 1 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  22 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 280)))))))))))))))))))))) (allB_succ
  21 280 (allA_succ_of_accept 20 21 280 (accept_3_3 20 21 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 280 (accept_3_3 17 21 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16
  21 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 21 280 7 2 3 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 21 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 280 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 21
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 280 (accept_3_3 11 21 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074
  10 21 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 280
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 21 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 280 (accept_3_3 8 21 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 280
  7 1 3 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 21 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 280 (accept_3_3 5 21 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 21 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 21 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 280 (accept_3_3 2 21 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 280))))))))))))))))))))) (allB_succ 20 280 (allA_of_3_1 20 20
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 280 (allA_succ_of_accept 18 19 280
  (Polychromatic418967fa.accept_21_18_19_7_1_5165 18 19 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 280 (accept_3_3 17 19 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 280 (Polychromatic418967fa.accept_17_16_2_8_1_7625 16 19 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 280 (accept_3_3 14 19 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 19 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 280
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 19 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 280 (accept_3_3 11 19 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 19 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 280 (accept_3_3 8 19 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 19 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 280
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 6 19 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 280 (accept_3_3 5 19 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  280 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 19 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 280 (accept_3_3 2 19 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 19 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 280))))))))))))))))))) (allB_succ 18 280
  (allA_succ_of_accept 17 18 280 (accept_3_3 17 18 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18
  280 2 8 9 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  18 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 18 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 18 280 2 7 9 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 280 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 18 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 280 2 6 9 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 280 (accept_3_3 11 18 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 280 2 5 9 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 18 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 18 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 280 2 4 9 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 280
  (Polychromatic418967fa.accept_15_7_3_10_1_817 7 18 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 280 2 3 9 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 280 (accept_3_3 5 18 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 280
  2 2 9 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18
  280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 18 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 280 2 1 9 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 280 (Polychromatic418967fa.accept_19_1_18_14_1_6392 1 18 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 280)))))))))))))))))) (allB_succ 17 280 (allA_of_3_1 17 17 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 280 (allA_succ_of_accept 15 16 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 16 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 280 2 7 8 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 16 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 280 4 3 4 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 280 (accept_3_3 11 16 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 280 2 5 8 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 16 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 280 8 1 2 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 7
  16 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 280 2 3 8 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 280 (accept_3_3 5 16
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 280 4 1 4 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 16 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 280 2 1 8 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 16 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 280)))))))))))))))) (allB_succ 15 280 (allA_succ_of_accept 14 15 280
  (accept_3_3 14 15 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 15 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 280 (accept_3_3 11 15 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 15 280 5 2 3 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 15 280 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 15 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 280 (accept_3_3 8 15 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 15 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 280 5 1 3 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 15 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 15 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 280 (accept_3_3 2 15 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 280))))))))))))))) (allB_succ 14 280
  (allA_of_3_1 14 14 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 280 (allA_succ_of_accept 12 13 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 13 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 280 (accept_3_3 11 13 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 13 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 280 (accept_3_3 8 13 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 280 (accept_3_3 5 13 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 13 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 280 (accept_3_3 2 13 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 13 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 280))))))))))))) (allB_succ 12 280
  (allA_succ_of_accept 11 12 280 (accept_3_3 11 12 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  280 2 5 6 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  12 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 12 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 12 280 4 2 3 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 280 2 3 6 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 280 (accept_3_3 5 12 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 280 4 1 3 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 12 280 (Polychromatic418967fa.accept_16_3_12_8_1_808 3 12 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 280 2 1 6 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 280
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 12 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 280)))))))))))) (allB_succ 11 280 (allA_of_3_1 11 11 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 280 (allA_succ_of_accept 9 10 280 (Polychromatic418967fa.accept_21_9_10_7_1_383 9 10 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 280 2 4 5 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 10 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 280 2 3 5 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 10 280 5 1 2 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 10 280 2 2 5 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 10 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 10 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 280 2 1 5 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 10 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 280)))))))))) (allB_succ 9 280
  (allA_succ_of_accept 8 9 280 (accept_3_3 8 9 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 9 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 9 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 280 (accept_3_3 5 9 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 9 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3
  9 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 280 (accept_3_3 2 9 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 280))))))))) (allB_succ 8 280
  (allA_of_3_1 8 8 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 280 (allA_succ_of_accept 6 7 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 280 (accept_3_3 5 7 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 280 (accept_3_3 2 7 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 7 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 280))))))) (allB_succ 6 280 (allA_succ_of_accept 5 6 280
  (accept_3_3 5 6 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 280 2 2 3 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 6 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 280 2 1 3 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 6 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 280)))))) (allB_succ 5 280 (allA_of_3_1 5 5 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 280 (allA_succ_of_accept 3 4 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 4 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 280 2 1 2 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 4 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 280)))) (allB_succ 3 280 (allA_succ_of_accept 2 3 280 (accept_3_3 2 3 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 280))) (allB_succ 2 280 (allA_of_3_1 2 2 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


